/** Module name: vtb_offchain
 *Description: It has code implementation with offchain worker to get and post http request
 *Methods: fetch_n_parse_get_request, fetch_from_remote_get_request, fetch_n_parse_post_request, fetch_from_remote_post_request
 *Method: fetch_eos_current_block_number - to get current block number from ethereum network
 *Method: append_or_replace_current_eos_block_number - It is to maintian last 10 current eos_blocknumber record in offchain storage
 **/
 use sp_runtime::{
     offchain as rt_offchain,
 };
 use sp_std::{ prelude::*, str,};
 use primitive_types::U256;
 use crate::Error;
 use crate::Pallet;
 use crate::Config;
 
 const FETCH_TIMEOUT_PERIOD: u64 = 3000; // in milli-seconds

 impl<T: Config> Pallet<T> {
 
    /// Parse the price from the given JSON string using `lite-json`.
	/// Returns `None` when parsing failed or `Some(price in cents)` when parsing is successful.
	pub fn parse_eth_price(req_url: &str) -> Option<U256> {

		let resp_bytes = Self::fetch_from_remote_get_request(req_url).map_err(|e| {
            log::info!("fetch_from_remote error: {:?}", e);
            <Error<T>>::HttpFetchingError
        }).ok()?;

		let price_str = sp_std::str::from_utf8(&resp_bytes).map_err(|_| {
			log::warn!("No UTF8 body");
			<Error<T>>::ByteToStringConversionError
		}).ok()?;

        let val =
        serde_json::from_str(price_str).map_err(|_| <Error<T>>::StringParsingError);

		let price = match val.ok()? {
			serde_json::Value::Object(obj) => {
				let (_, v) = obj.into_iter().find(|(k, _)| k.eq("ethRateInt"))?;
				match v {
					serde_json::Value::String(number) => U256::from_dec_str(&number).unwrap(),
					_ => return None,
				}
			},
			_ => return None,
		};

        Some(price)
	}

    pub(super) fn fetch_average_eth_price() -> Option<U256> {
        let eth_price1 = Self::parse_eth_crypto_compare_price()?;
        let eth_price2 = Self::parse_eth_etherscan_price_price()?;
        let eth_average = (eth_price1 + eth_price2)/2_f64;
        Some(U256::from(eth_average as u128))
    }
    
    /// Parse the price from the given JSON string using `lite-json` from `CryptoCompare`.
	/// Returns `None` when parsing failed or `Some(price in cents)` when parsing is successful.
	fn parse_eth_crypto_compare_price() -> Option<f64> {

        let crypto_compare_req_url = "https://min-api.cryptocompare.com/data/price?fsym=ETH&tsyms=ETH,USD,EUR";
		let resp_bytes = Self::fetch_from_remote_get_request(crypto_compare_req_url).map_err(|e| {
            log::info!("fetch_from_remote error: {:?}", e);
            <Error<T>>::HttpFetchingError
        }).ok()?;

		let price_str = sp_std::str::from_utf8(&resp_bytes).map_err(|_| {
			log::warn!("No UTF8 body");
			<Error<T>>::ByteToStringConversionError
		}).ok()?;

        let val =
        serde_json::from_str(price_str).map_err(|_| <Error<T>>::StringParsingError);

		let price = match val.ok()? {
			serde_json::Value::Object(obj) => {
				let (_, v) = obj.into_iter().find(|(k, _)| k.eq("USD"))?;
				match v {
					serde_json::Value::Number(number) => {
                    let precision = 1_000_000_000_000_000_000.00;
                    number.as_f64().unwrap() * precision
                },
					_ => return None,
				}
			},
			_ => return None,
		};

        Some(price)
	}

    /// Parse the price from the given JSON string using `lite-json` from `Etherscan`.
	/// Returns `None` when parsing failed or `Some(price in cents)` when parsing is successful.
	fn parse_eth_etherscan_price_price() -> Option<f64> {

        let etherscan_req_url = "https://api.etherscan.io/api?module=stats&action=ethprice&apikey=QBEZKHAANWJBU2JXSKXMZXVDHYJRJ6SND7";
    
		let resp_bytes = Self::fetch_from_remote_get_request(etherscan_req_url).map_err(|e| {
            log::info!("fetch_from_remote error: {:?}", e);
            <Error<T>>::HttpFetchingError
        }).ok()?;

		let price_str = sp_std::str::from_utf8(&resp_bytes).map_err(|_| {
			log::warn!("No UTF8 body");
			<Error<T>>::ByteToStringConversionError
		}).ok()?;

        let val =
        serde_json::from_str(price_str).map_err(|_| <Error<T>>::StringParsingError);

		let price = match val.ok()? {
			serde_json::Value::Object(obj) => {
				let (_, v) = obj.into_iter().find(|(k, _)| k.eq("result"))?;
                match v {
                    serde_json::Value::Object(obj) => {
                        let (_, p) = obj.into_iter().find(|(k, _)| k.eq("ethusd"))?;
                        match p {
                            serde_json::Value::String(number) => {
                            let precision = 1_000_000_000_000_000_000.00;
                            let f = number.parse::<f64>().unwrap();
                            f * precision
                        },
                            _ => return None,
                        }
                    },
                    _ => return None,
                }
				
			},
			_ => return None,
		};

        Some(price)
	}

    /// Parse the price from the given JSON string using `lite-json`.
	/// Returns `None` when parsing failed or `Some(price in cents)` when parsing is successful.
	pub fn parse_eos_price(req_url: &str) -> Option<U256> {

		let resp_bytes = Self::fetch_from_remote_get_request(req_url).map_err(|e| {
            log::info!("fetch_from_remote error: {:?}", e);
            <Error<T>>::HttpFetchingError
        }).ok()?;

		let price_str = sp_std::str::from_utf8(&resp_bytes).map_err(|_| {
			log::warn!("No UTF8 body");
			<Error<T>>::ByteToStringConversionError
		}).ok()?;

        let val =
        serde_json::from_str(price_str).map_err(|_| <Error<T>>::StringParsingError);

		let price = match val.ok()? {
			serde_json::Value::Object(obj) => {
				let (_, v) = obj.into_iter().find(|(k, _)| k.eq("USD"))?;
				match v {
					serde_json::Value::Number(number) => {
                        let precision = 1000000000000000000.00;
                        number.as_f64().unwrap() * precision
                    },
					_ => return None,
				}
			},
			_ => return None,
		};

        Some(U256::from(price as u128 ))
	}

    /// Fetch from remote and deserialize the JSON to a struct
    pub fn fetch_n_parse_get_request(req_url: &str) -> Result<serde_json::Value, Error<T>> {
 
        let resp_bytes = Self::fetch_from_remote_get_request(req_url).map_err(|e| {
            log::info!("fetch_from_remote error: {:?}", e);
            <Error<T>>::HttpFetchingError
        })?;

        let resp_str = str::from_utf8(&resp_bytes).map_err(|_| <Error<T>>::ByteToStringConversionError)?;
        // Print out our fetched JSON string
        log::info!("{}", resp_str);

        let http_resp: serde_json::Value =
        serde_json::from_str(resp_str).map_err(|_| <Error<T>>::StringParsingError)?;

        Ok(http_resp)
    }

    /// This function uses the `offchain::http` API to query the remote github information,
    ///   and returns the JSON response as vector of bytes.
    pub fn fetch_from_remote_get_request(req_url: &str) -> Result<Vec<u8>, Error<T>> {
        // Initiate an external HTTP GET request. This is using high-level wrappers from `sp_runtime`.
        let request = rt_offchain::http::Request::get(req_url);
        
        // Keeping the offchain worker execution time reasonable, so limiting the call to be within 3s.
        let timeout = sp_io::offchain::timestamp()
            .add(rt_offchain::Duration::from_millis(FETCH_TIMEOUT_PERIOD));

        let pending = request
            .deadline(timeout) // Setting the timeout time
            .send() // Sending the request out by the host
            .map_err(|_| <Error<T>>::HttpFetchingError)?;

        // By default, the http request is async from the runtime perspective. So we are asking the
        //   runtime to wait here.
        // The returning value here is a `Result` of `Result`, so we are unwrapping it twice by two `?`
        //   ref: https://substrate.dev/rustdocs/v3.0.0/sp_runtime/offchain/http/struct.PendingRequest.html#method.try_wait
        let response = pending
            .try_wait(timeout)
            .map_err(|_| <Error<T>>::HttpFetchingError)?
            .map_err(|_| <Error<T>>::HttpFetchingError)?;

        if response.code != 200 {
            log::info!("Unexpected http request status code: {}", response.code);
            return Err(<Error<T>>::HttpFetchingError);
        }
        // Next we fully read the response body and collect it to a vector of bytes.
        Ok(response.body().collect::<Vec<u8>>())
    }

} 