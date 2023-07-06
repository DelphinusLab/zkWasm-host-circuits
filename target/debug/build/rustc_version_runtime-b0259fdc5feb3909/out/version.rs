
            /// Returns the `rustc` SemVer version and additional metadata
            /// like the git short hash and build date.
            pub fn version_meta() -> VersionMeta {
                VersionMeta {
                    semver: Version {
                        major: 1,
                        minor: 67,
                        patch: 0,
                        pre: vec![semver::Identifier::AlphaNumeric("nightly".to_owned()), ],
                        build: vec![],
                    },
                    host: "aarch64-apple-darwin".to_owned(),
                    short_version_string: "rustc 1.67.0-nightly (e0098a5cc 2022-11-29)".to_owned(),
                    commit_hash: Some("e0098a5cc3a87d857e597af824d0ce1ed1ad85e0".to_owned()),
                    commit_date: Some("2022-11-29".to_owned()),
                    build_date: None,
                    channel: Channel::Nightly,
                }
            }
            