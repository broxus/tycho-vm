use ahash::{HashMap, HashSet};
use anyhow::Result;
use everscale_types::error::Error;
use everscale_types::models::{
    BlockchainConfig, BurningConfig, GasLimitsPrices, GlobalVersion, MsgForwardPrices,
    SizeLimitsConfig, StdAddr, StorageInfo, StoragePrices, WorkchainDescription,
};
use everscale_types::num::Tokens;
use everscale_types::prelude::*;
use tycho_vm::{GasParams, UnpackedConfig};

use crate::util::shift_ceil_price;

/// Parsed [`BlockchainConfigParams`].
pub struct ParsedConfig {
    pub blackhole_addr: Option<HashBytes>,
    pub mc_gas_prices: GasLimitsPrices,
    pub gas_prices: GasLimitsPrices,
    pub mc_fwd_prices: MsgForwardPrices,
    pub fwd_prices: MsgForwardPrices,
    pub size_limits: SizeLimitsConfig,
    pub storage_prices: Vec<StoragePrices>,
    pub global_id: i32,
    pub global: GlobalVersion,
    pub workchains: HashMap<i32, WorkchainDescription>,
    pub special_accounts: HashSet<HashBytes>,
    pub raw: BlockchainConfig,
    pub unpacked: UnpackedConfig,
}

impl ParsedConfig {
    // TODO: Pass `global_id` here as well? For now we assume that
    //       `params` will contain a global id entry (`ConfigParam19`).
    // TODO: Return error if storage prices `utime_since` is not properly sorted.
    pub fn parse(config: BlockchainConfig, now: u32) -> Result<Self, Error> {
        let dict = config.params.as_dict();

        let burning = dict.get(5).and_then(|cell| match cell {
            Some(cell) => cell.parse::<BurningConfig>(),
            None => Ok(BurningConfig::default()),
        })?;

        let Some(mc_gas_prices_raw) = dict.get(20)? else {
            return Err(Error::CellUnderflow);
        };
        let Some(gas_prices_raw) = dict.get(21)? else {
            return Err(Error::CellUnderflow);
        };

        let Some(mc_fwd_prices_raw) = dict.get(24)? else {
            return Err(Error::CellUnderflow);
        };
        let Some(fwd_prices_raw) = dict.get(25)? else {
            return Err(Error::CellUnderflow);
        };

        let storage_prices_dict = RawDict::<32>::from(dict.get(18)?);
        let mut storage_prices = Vec::new();
        let mut latest_storage_prices = None;
        for value in storage_prices_dict.values_owned() {
            let value = value?;
            let prices = StoragePrices::load_from(&mut value.1.apply_allow_exotic(&value.0))?;
            if prices.utime_since <= now {
                latest_storage_prices = Some(value);
            }

            storage_prices.push(prices);
        }

        let workchains_dict = config.params.get_workchains()?;
        let mut workchains = HashMap::<i32, WorkchainDescription>::default();
        for entry in workchains_dict.iter() {
            let (workchain, desc) = entry?;
            workchains.insert(workchain, desc);
        }

        let global_id_raw = dict.get(19)?;
        let global = config.params.get_global_version()?;

        // Fallback to default if param not present in config?
        let Some(size_limits_raw) = dict.get(43)? else {
            return Err(Error::CellUnderflow);
        };

        let mut special_accounts = HashSet::default();
        for addr in config.params.get_fundamental_addresses()?.keys() {
            special_accounts.insert(addr?);
        }

        Ok(Self {
            blackhole_addr: burning.blackhole_addr,
            mc_gas_prices: mc_gas_prices_raw.parse::<GasLimitsPrices>()?,
            gas_prices: gas_prices_raw.parse::<GasLimitsPrices>()?,
            mc_fwd_prices: mc_fwd_prices_raw.parse::<MsgForwardPrices>()?,
            fwd_prices: fwd_prices_raw.parse::<MsgForwardPrices>()?,
            size_limits: size_limits_raw.parse::<SizeLimitsConfig>()?,
            storage_prices,
            global_id: match &global_id_raw {
                None => 0, // Return error?
                Some(param) => param.parse::<i32>()?,
            },
            global,
            workchains,
            special_accounts,
            raw: config,
            unpacked: UnpackedConfig {
                latest_storage_prices,
                global_id: global_id_raw,
                mc_gas_prices: Some(mc_gas_prices_raw),
                gas_prices: Some(gas_prices_raw),
                mc_fwd_prices: Some(mc_fwd_prices_raw),
                fwd_prices: Some(fwd_prices_raw),
                size_limits_config: Some(size_limits_raw),
            },
        })
    }

    pub fn is_blackhole(&self, addr: &StdAddr) -> bool {
        match &self.blackhole_addr {
            Some(blackhole_addr) => addr.is_masterchain() && addr.address == *blackhole_addr,
            None => false,
        }
    }

    pub fn is_special(&self, addr: &StdAddr) -> bool {
        addr.is_masterchain()
            && (self.special_accounts.contains(&addr.address) || addr.address == self.raw.address)
    }

    pub fn fwd_prices(&self, is_masterchain: bool) -> &MsgForwardPrices {
        if is_masterchain {
            &self.mc_fwd_prices
        } else {
            &self.fwd_prices
        }
    }

    pub fn gas_prices(&self, is_masterchain: bool) -> &GasLimitsPrices {
        if is_masterchain {
            &self.mc_gas_prices
        } else {
            &self.gas_prices
        }
    }

    /// Computes fees of storing `storage_stat.used` bits and refs
    /// since `storage_stat.last_paid` and up until `now`.
    ///
    /// NOTE: These fees don't include `due_payment`.
    pub fn compute_storage_fees(
        &self,
        storage_stat: &StorageInfo,
        now: u32,
        is_special: bool,
        is_masterchain: bool,
    ) -> Tokens {
        // No fees in following cases:
        // - Time has not moved forward since the last transaction;
        // - Account was just created (last_paid: 0);
        // - Special accounts;
        // - No storage prices.
        if now <= storage_stat.last_paid || storage_stat.last_paid == 0 || is_special {
            return Tokens::ZERO;
        }

        let Some(oldest_prices) = self.storage_prices.first() else {
            // No storage prices.
            return Tokens::ZERO;
        };
        if now <= oldest_prices.utime_since {
            // No storage prices (being active for long enought time).
            return Tokens::ZERO;
        }

        let get_prices = if is_masterchain {
            |prices: &StoragePrices| (prices.mc_bit_price_ps, prices.mc_cell_price_ps)
        } else {
            |prices: &StoragePrices| (prices.bit_price_ps, prices.cell_price_ps)
        };

        let mut total = 0u128;

        // Sum fees for all segments (starting from the most recent).
        let mut upto = now;
        for prices in self.storage_prices.iter().rev() {
            if prices.utime_since > upto {
                continue;
            }

            // Compute for how long the segment was active
            let delta = upto - std::cmp::max(prices.utime_since, storage_stat.last_paid);

            // Sum fees
            let (bit_price, cell_price) = get_prices(prices);
            let fee = (bit_price as u128 * storage_stat.used.bits.into_inner() as u128)
                .saturating_add(cell_price as u128 * storage_stat.used.cells.into_inner() as u128)
                .saturating_mul(delta as u128);
            total = total.saturating_add(fee);

            // Stop on the first outdated segment.
            upto = prices.utime_since;
            if upto <= storage_stat.last_paid {
                break;
            }
        }

        // Convert from fixed point int.
        Tokens::new(shift_ceil_price(total))
    }

    /// Computes gas credit and limits bought for the provided balances.
    pub fn compute_gas_params(
        &self,
        account_balance: &Tokens,
        msg_balance_remaining: &Tokens,
        is_special: bool,
        is_masterchain: bool,
        is_tx_ordinary: bool,
        is_in_msg_external: bool,
    ) -> GasParams {
        let prices = self.gas_prices(is_masterchain);

        let gas_max = if is_special {
            prices.special_gas_limit
        } else {
            gas_bought_for(prices, account_balance)
        };

        let gas_limit = if !is_tx_ordinary || is_special {
            // May use all gas that can be bought using remaining balance.
            gas_max
        } else {
            // Use only gas bought using remaining message balance.
            // If the message is "accepted" by the smart contract,
            // the gas limit will be set to `gas_max`.
            std::cmp::min(gas_bought_for(prices, msg_balance_remaining), gas_max)
        };

        let gas_credit = if is_tx_ordinary && is_in_msg_external {
            // External messages carry no balance,
            // give them some credit to check whether they are accepted.
            std::cmp::min(prices.gas_credit, gas_max)
        } else {
            0
        };

        GasParams {
            max: gas_max,
            limit: gas_limit,
            credit: gas_credit,
            price: prices.gas_price,
        }
    }
}

fn gas_bought_for(prices: &GasLimitsPrices, balance: &Tokens) -> u64 {
    let balance = balance.into_inner();
    if balance == 0 || balance < prices.flat_gas_price as u128 {
        return 0;
    }

    let max_gas_threshold = if prices.gas_limit > prices.flat_gas_limit {
        shift_ceil_price(
            (prices.gas_price as u128) * (prices.gas_limit - prices.flat_gas_limit) as u128,
        )
        .saturating_add(prices.flat_gas_price as u128)
    } else {
        prices.flat_gas_price as u128
    };

    if balance >= max_gas_threshold || prices.gas_price == 0 {
        return prices.gas_limit;
    }

    let mut res = ((balance - prices.flat_gas_price as u128) << 16) / (prices.gas_price as u128);
    res = res.saturating_add(prices.flat_gas_limit as u128);

    match res.try_into() {
        Ok(limit) => limit,
        Err(_) => u64::MAX,
    }
}
