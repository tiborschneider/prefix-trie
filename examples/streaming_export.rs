//! Streaming binary export and import of a `PrefixMap` and `JointPrefixMap`.
//!
//! This example demonstrates how to serialize a prefix trie to a file (or any
//! `std::io::Write`) record-by-record, and deserialize it back from a file (or
//! any `std::io::Read`) record-by-record.  This is useful for large routing
//! tables where loading the entire serialized blob into memory is undesirable.
//!
//! The `serde` feature on `prefix-trie` provides `Serialize`/`Deserialize` for
//! `PrefixMap` and `JointPrefixMap`.  Combined with a binary serde format such
//! as [`bincode`](https://crates.io/crates/bincode), you get a compact,
//! streaming-friendly serialization.
//!
//! Run with:
//!
//! ```bash
//! cargo run --example streaming_export --features ipnet,serde
//! ```

use std::io::{BufReader, BufWriter, Cursor, Write as _};

use ipnet::Ipv4Net;
use prefix_trie::{joint::JointPrefixMap, PrefixMap};

// The `serde` feature on `prefix-trie` implements `serde::Serialize` and
// `serde::Deserialize` for `PrefixMap` and `JointPrefixMap`.  `bincode`'s serde
// bridge (`bincode::serde`) then provides the actual binary encoding.

/// Serialize all `(prefix, value)` entries to a writer, one record at a time.
///
/// Each entry is independently encoded, so the writer can be a file, a socket,
/// or any `std::io::Write`.  The reader side can stop at EOF without knowing
/// the number of records in advance.
fn export_to_writer<P, T, W>(
    map: &PrefixMap<P, T>,
    writer: W,
) -> Result<(), Box<dyn std::error::Error>>
where
    P: serde::Serialize + prefix_trie::Prefix,
    T: serde::Serialize,
    W: std::io::Write,
{
    let config = bincode::config::standard();
    let mut writer = BufWriter::new(writer);
    for (prefix, value) in map.iter() {
        bincode::serde::encode_into_std_write(&(prefix, value), &mut writer, config)?;
    }
    writer.flush()?;
    Ok(())
}

/// Deserialize entries from a reader and rebuild a `PrefixMap`.
///
/// Reads one `(prefix, value)` record at a time until EOF.  The returned map
/// is functionally identical to the one that was exported.
fn import_from_reader<P, T, R>(reader: R) -> Result<PrefixMap<P, T>, Box<dyn std::error::Error>>
where
    P: serde::de::DeserializeOwned + prefix_trie::Prefix,
    T: serde::de::DeserializeOwned,
    R: std::io::Read,
{
    let config = bincode::config::standard();
    let mut reader = BufReader::new(reader);
    let mut map = PrefixMap::new();
    loop {
        match bincode::serde::decode_from_std_read::<(P, T), _, _>(&mut reader, config) {
            Ok((prefix, value)) => {
                map.insert(prefix, value);
            }
            Err(bincode::error::DecodeError::Io { inner, .. })
                if inner.kind() == std::io::ErrorKind::UnexpectedEof =>
            {
                break; // clean EOF — all records consumed
            }
            Err(e) => return Err(e.into()),
        }
    }
    Ok(map)
}

/// Serialize a `JointPrefixMap` to a writer, interleaving both address families.
fn export_joint_to_writer<P, T, W>(
    map: &JointPrefixMap<P, T>,
    writer: W,
) -> Result<(), Box<dyn std::error::Error>>
where
    P: serde::Serialize + prefix_trie::joint::JointPrefix,
    T: serde::Serialize,
    W: std::io::Write,
{
    let config = bincode::config::standard();
    let mut writer = BufWriter::new(writer);
    for (prefix, value) in map.iter() {
        bincode::serde::encode_into_std_write(&(prefix, value), &mut writer, config)?;
    }
    writer.flush()?;
    Ok(())
}

/// Deserialize entries from a reader and rebuild a `JointPrefixMap`.
fn import_joint_from_reader<P, T, R>(
    reader: R,
) -> Result<JointPrefixMap<P, T>, Box<dyn std::error::Error>>
where
    P: serde::de::DeserializeOwned + prefix_trie::joint::JointPrefix,
    T: serde::de::DeserializeOwned,
    R: std::io::Read,
{
    let config = bincode::config::standard();
    let mut reader = BufReader::new(reader);
    let mut map = JointPrefixMap::new();
    loop {
        match bincode::serde::decode_from_std_read::<(P, T), _, _>(&mut reader, config) {
            Ok((prefix, value)) => {
                map.insert(prefix, value);
            }
            Err(bincode::error::DecodeError::Io { inner, .. })
                if inner.kind() == std::io::ErrorKind::UnexpectedEof =>
            {
                break;
            }
            Err(e) => return Err(e.into()),
        }
    }
    Ok(map)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // ── PrefixMap ──────────────────────────────────────────────────────

    let mut pm: PrefixMap<Ipv4Net, String> = PrefixMap::new();
    pm.insert("10.0.0.0/8".parse()?, "backbone".into());
    pm.insert("10.1.0.0/16".parse()?, "edge".into());
    pm.insert("192.168.1.0/24".parse()?, "lan".into());

    // Serialize to an in-memory buffer (could be a File, a socket, etc.)
    let mut buf = Vec::new();
    export_to_writer(&pm, &mut buf)?;
    println!(
        "PrefixMap: serialized {} bytes for {} entries",
        buf.len(),
        pm.len()
    );

    // Deserialize back
    let restored = import_from_reader::<Ipv4Net, String, _>(Cursor::new(&buf))?;
    assert_eq!(restored.len(), pm.len());
    for (prefix, value) in pm.iter() {
        assert_eq!(restored.get(&prefix), Some(value));
    }
    println!("PrefixMap: round-trip OK");

    // ── JointPrefixMap ─────────────────────────────────────────────────

    let mut jpm: JointPrefixMap<ipnet::IpNet, u32> = JointPrefixMap::new();
    jpm.insert("10.0.0.0/8".parse()?, 100);
    jpm.insert("2001:db8::/32".parse()?, 200);

    let mut jbuf = Vec::new();
    export_joint_to_writer(&jpm, &mut jbuf)?;
    println!(
        "JointPrefixMap: serialized {} bytes for {} entries",
        jbuf.len(),
        jpm.len()
    );

    let jrestored = import_joint_from_reader::<ipnet::IpNet, u32, _>(Cursor::new(&jbuf))?;
    assert_eq!(jrestored.len(), jpm.len());
    println!("JointPrefixMap: round-trip OK");

    Ok(())
}
