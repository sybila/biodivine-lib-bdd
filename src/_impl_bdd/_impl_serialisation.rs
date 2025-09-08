use crate::*;
use std::fmt::{Display, Formatter};
use std::io;
use std::io::{ErrorKind, Read, Write};

/// Serialisation and deserialization methods for `Bdd`s.
impl Bdd {
    /// Write this `Bdd` into the given `output` writer using a simple string format.
    pub fn write_as_string<W: Write>(&self, output: &mut W) -> Result<(), io::Error> {
        write!(output, "|")?;
        for node in self.nodes() {
            write!(output, "{},{},{}|", node.var, node.low_link, node.high_link)?;
        }
        Ok(())
    }

    /// Read a `Bdd` from the given `input` reader, assuming a simple string format.
    pub fn read_as_string<R: Read>(input: &mut R) -> Result<Bdd, String> {
        let mut data = String::new();
        lift_err(input.read_to_string(&mut data))?;
        data.retain(|c| !c.is_whitespace()); // Ignore whitespace when parsing.
        let mut result = Vec::new();
        for node_string in data.split('|').filter(|s| !s.is_empty()) {
            let node_items: Vec<&str> = node_string.split(',').collect();
            let node = BddNode::mk_node(
                BddVariable(lift_err(node_items[0].parse::<u16>())?),
                BddPointer::from_index(lift_err(node_items[1].parse::<usize>())?),
                BddPointer::from_index(lift_err(node_items[2].parse::<usize>())?),
            );
            result.push(node);
        }
        Ok(Bdd(result))
    }

    /// Write this `Bdd` into the given `output` writer using a simple little-endian binary encoding.
    pub fn write_as_bytes<W: Write>(&self, output: &mut W) -> Result<(), io::Error> {
        for node in self.nodes() {
            output.write_all(&node.var.to_le_bytes())?;
            output.write_all(&node.low_link.to_le_bytes())?;
            output.write_all(&node.high_link.to_le_bytes())?;
        }
        Ok(())
    }

    /// Read a `Bdd` from a given `input` reader using a simple little-endian binary encoding.
    pub fn read_as_bytes<R: Read>(input: &mut R) -> Result<Bdd, io::Error> {
        let mut result = Vec::new();
        let mut buf = [0u8; 10];
        loop {
            // Admittedly, this can miss some errors in truncated files, but unfortunately the
            // "read" method may return an incomplete buffer when blocking IO is involved.
            // So this is the best I can do right now.
            match input.read_exact(&mut buf) {
                Ok(_) => (),
                Err(e) => {
                    return if e.kind() == ErrorKind::UnexpectedEof {
                        Ok(Bdd(result))
                    } else {
                        Err(e)
                    };
                }
            }

            result.push(BddNode::mk_node(
                BddVariable::from_le_bytes([buf[0], buf[1]]),
                BddPointer::from_le_bytes([buf[2], buf[3], buf[4], buf[5]]),
                BddPointer::from_le_bytes([buf[6], buf[7], buf[8], buf[9]]),
            ));
        }
    }

    /// Read a `Bdd` from a serialized string.
    pub fn from_string(bdd: &str) -> Bdd {
        Bdd::read_as_string(&mut bdd.as_bytes()).expect("Invalid BDD string.")
    }

    /// Convert this `Bdd` to a byte vector.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buffer = Vec::new();
        self.write_as_bytes(&mut buffer)
            .expect("Error writing bytes.");
        buffer
    }

    /// Read a `Bdd` from a byte vector.
    pub fn from_bytes(data: &mut &[u8]) -> Bdd {
        Bdd::read_as_bytes(data).expect("Error reading bytes.")
    }
}

impl Display for Bdd {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        let mut buffer: Vec<u8> = Vec::new();
        self.write_as_string(&mut buffer)
            .expect("Cannot write BDD to string.");
        f.write_str(&String::from_utf8(buffer).expect("Invalid UTF formatting in string."))
    }
}

fn lift_err<T, E: ToString>(item: Result<T, E>) -> Result<T, String> {
    item.map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use crate::_test_util::{load_expected_results, mk_small_test_bdd};
    use crate::*;
    use std::fs::File;
    use std::io::{BufReader, BufWriter};

    #[test]
    fn read_bdd_with_whitespace() {
        let bdd = mk_small_test_bdd();
        let mut bdd_string = bdd.to_string();
        bdd_string = bdd_string.replace("|", "\t|");
        bdd_string = format!("\n\t\n{bdd_string}\n");
        let bdd2 = Bdd::from_string(bdd_string.as_str());
        assert_eq!(bdd, bdd2);
    }

    #[test]
    fn bdd_to_string() {
        let bdd = mk_small_test_bdd();
        let bdd_string = bdd.to_string();
        assert_eq!(load_expected_results("bdd_to_string.txt"), bdd_string);
    }

    #[test]
    fn bdd_from_string() {
        let data = load_expected_results("bdd_to_string.txt");
        let bdd = Bdd::from_string(&data);
        assert_eq!(mk_small_test_bdd(), bdd);
    }

    #[test]
    fn bdd_to_bytes() {
        let bdd = mk_small_test_bdd();
        let bdd_bytes = bdd.to_bytes();
        assert_eq!(bdd, Bdd::from_bytes(&mut &bdd_bytes[..]));
    }

    #[test]
    fn buffered_serialization() {
        let set = BddVariableSet::new_anonymous(50);
        let bdd = set.mk_sat_exactly_k(25, &set.variables());

        // Intentionally uses buffers of weird size to hopefully trigger a bug.
        // Also, it needs to actually use files, otherwise the buffered writers never block.
        // The blocking nature of file IO is essential.

        // Unfortunately, this still does not trigger the bug always. With sufficient file caching
        // and/or fast SSD, this might not trigger anything, but let's leave it here as
        // a cautionary tale to future generations.

        {
            let file = File::create("test.bdd").unwrap();
            let mut writer = BufWriter::with_capacity(3, file);
            bdd.write_as_bytes(&mut writer).unwrap();
        }

        let bdd_2 = {
            let file = File::open("test.bdd").unwrap();
            let mut reader = BufReader::with_capacity(3, file);
            Bdd::read_as_bytes(&mut reader).unwrap()
        };

        assert_eq!(bdd, bdd_2);
        std::fs::remove_file("test.bdd").unwrap();
    }
}
