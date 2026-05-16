# Test Data

## RIPE Routing Information System data
retrieved on: 2026-5-14

The benches use data derived from RIPE RIS raw data that is published as pre-procesed parquet files. The best current reference for this is [a presentation](https://pretalx.ripe.net/media/ripe91/submissions/3Q7AUL/resources/20251020_querying_the_VpHijNI.pdf).

### Processing summary

The original data was processed to create smaller test fixtures.

`20260511-initial-state-peer-193.0.0.56AS3333.parquet`: The IPv4 prefixes seen by a specific peer on 11-5-2026 at midnight.
`20260511-initial-state-peer-193.0.0.56AS3333-ipv6.parquet`: The IPv6 prefixes seen by the same peer at the same time.
`20260511-mutations-peer-193.0.0.56AS3333.parquet`: The IPv4 prefix and operation (A/W) for all BGP updates/withdraws seen by a specific peer.
`20260511-mutations-peer-193.0.0.56AS3333-ipv6.parquet`: The IPv6 prefix and operation (A/W) for the same updates/withdraws peer

It is a multi-protocol BGP session. IPv4 and IPv6 prefixes are split into separate fixtures.

### Reproduction steps

Use duckdb and the parquet files available under https://data.ris.ripe.net/derived/prototypes/parquet/v0/:

```
COPY(
  SELECT prefix
  FROM read_parquet('https://data.ris.ripe.net/derived/prototypes/parquet/v0/bview/year%3D2026/month%3D05/day%3D11/20260511.0000-bview-all-collectors.parquet')
  WHERE
    peer_ip = '193.0.0.56'
  AND
  ':' NOT IN prefix
  ORDER BY prefix ASC
) TO '20260511-initial-state-peer-193.0.0.56AS3333.parquet' (FORMAT PARQUET, COMPRESSION ZSTD, COMPRESSION_LEVEL 11);

COPY(
  SELECT prefix
  FROM read_parquet('https://data.ris.ripe.net/derived/prototypes/parquet/v0/bview/year%3D2026/month%3D05/day%3D11/20260511.0000-bview-all-collectors.parquet')
  WHERE
    peer_ip = '193.0.0.56'
  AND
  ':' IN prefix
  ORDER BY prefix ASC
) TO '20260511-initial-state-peer-193.0.0.56AS3333-ipv6.parquet' (FORMAT PARQUET, COMPRESSION ZSTD, COMPRESSION_LEVEL 11);

COPY(SELECT operation, prefix
         FROM read_parquet([
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=00.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=01.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=02.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=03.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=04.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=05.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=06.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=07.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=08.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=09.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=10.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=11.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=12.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=13.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=14.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=15.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=16.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=17.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=18.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=19.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=20.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=21.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=22.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=23.parquet'
         ], hive_partitioning = false)
         WHERE peer_ip = '193.0.0.56' AND ':' NOT IN prefix order by ts asc
) TO '20260511-mutations-peer-193.0.0.56AS3333.parquet' (FORMAT PARQUET, COMPRESSION ZSTD, COMPRESSION_LEVEL 11);

COPY(SELECT operation, prefix
         FROM read_parquet([
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=00.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=01.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=02.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=03.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=04.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=05.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=06.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=07.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=08.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=09.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=10.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=11.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=12.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=13.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=14.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=15.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=16.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=17.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=18.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=19.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=20.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=21.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=22.parquet',
           'https://data.ris.ripe.net/derived/prototypes/parquet/v0/updates/year%3D2026/month%3D05/day%3D11/hour=23.parquet'
         ], hive_partitioning = false)
         WHERE peer_ip = '193.0.0.56' AND ':' IN prefix order by ts asc
) TO '20260511-mutations-peer-193.0.0.56AS3333-ipv6.parquet' (FORMAT PARQUET, COMPRESSION ZSTD, COMPRESSION_LEVEL 11);
```
