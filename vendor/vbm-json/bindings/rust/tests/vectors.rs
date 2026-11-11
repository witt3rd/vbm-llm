// The Rust binding against the Lean reference: every row of the shared vectors (vbm-json-vectors-1; the JSONTestSuite files are set `jts`). A driver: it holds no input of its own (the deep, duplicate-key, lexeme and empty inputs are rows of the generated set); not part of the binding.
// VBM_JSON_VECTORS = the vectors.jsonl path (scripts/test_bindings.sh). An accepted input must parse and print (here) to the reference's canonical bytes; a rejected one must be the reference's code.
use vbm_json::{compact, escape_string, parse, Error, Value};

fn field<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    let pat = format!("\"{}\":\"", key);
    let s = line.find(&pat)? + pat.len();
    Some(&line[s..s + line[s..].find('"')?])
}
fn unhex(h: &str) -> Vec<u8> { (0..h.len() / 2).map(|i| u8::from_str_radix(&h[2 * i..2 * i + 2], 16).unwrap()).collect() }
fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{:02x}", x)).collect() }

fn canon(v: &Value, o: &mut Vec<u8>) {
    match v {
        Value::Null => o.extend_from_slice(b"null"),
        Value::Bool(b) => o.extend_from_slice(if *b { b"true" } else { b"false" }),
        Value::Number(n) => o.extend_from_slice(n.as_bytes()),
        Value::String(s) => {
            o.push(b'"');
            for &c in s.as_bytes() {
                match c {
                    0x22 => o.extend_from_slice(b"\\\""), 0x5C => o.extend_from_slice(b"\\\\"), 8 => o.extend_from_slice(b"\\b"), 12 => o.extend_from_slice(b"\\f"),
                    10 => o.extend_from_slice(b"\\n"), 13 => o.extend_from_slice(b"\\r"), 9 => o.extend_from_slice(b"\\t"),
                    c if c < 0x20 => o.extend_from_slice(format!("\\u00{:02x}", c).as_bytes()),
                    c => o.push(c),
                }
            }
            o.push(b'"');
        }
        Value::Array(xs) => { o.push(b'['); for (i, x) in xs.iter().enumerate() { if i > 0 { o.push(b','); } canon(x, o); } o.push(b']'); }
        Value::Object(ms) => {
            o.push(b'{');
            for (i, (k, x)) in ms.iter().enumerate() { if i > 0 { o.push(b','); } canon(&Value::String(k.clone()), o); o.push(b':'); canon(x, o); }
            o.push(b'}');
        }
    }
}

fn input_text(v: &Value) -> Vec<u8> { match v { Value::String(s) => s.as_bytes().to_vec(), _ => unreachable!() } }

#[test]
fn shared_vectors() {
    let path = std::env::var("VBM_JSON_VECTORS").expect("VBM_JSON_VECTORS: the vectors.jsonl path");
    let text = std::fs::read_to_string(path).unwrap();
    let (mut rows, mut ok, mut errs, mut jts) = (0, 0, 0, 0);
    for line in text.lines() {
        rows += 1;
        if field(line, "set") == Some("jts") { jts += 1; }
        let input = unhex(field(line, "input").unwrap());
        let verdict = field(line, "verdict").unwrap();
        let id = format!("{} #{}", field(line, "set").unwrap(), line.split("\"id\":").nth(1).unwrap().split(',').next().unwrap());
        match parse(&input) {
            Ok(v) => {
                assert_eq!(verdict, "ok", "{}: expected an error, but it parsed", id);
                let mut o = Vec::new(); canon(&v, &mut o);
                assert_eq!(hex(&o), field(line, "canonical").unwrap(), "{}: canonical form differs", id);
                assert_eq!(hex(&compact(&input).unwrap()), field(line, "canonical").unwrap(), "{}: compact() differs from the canonical form", id);
                if let Value::String(_) = v { assert_eq!(hex(&escape_string(&input_text(&v)).unwrap()), field(line, "canonical").unwrap(), "{}: escape_string differs", id); }
                ok += 1;
            }
            Err(e) => {
                assert_eq!(verdict, "err", "{}: expected ok, got {}", id, e);
                let want = match field(line, "code").unwrap() { "syntax" => Error::Syntax, "depth" => Error::Depth, c => panic!("{}: code {}", id, c) };
                assert_eq!(e, want, "{}: wrong error code", id);
                errs += 1;
            }
        }
    }
    assert_eq!(escape_string(&[0xff]), Err(Error::Syntax), "escape_string accepted a byte that is not UTF-8");
    println!("vectors: {} rows ({} from the JSONTestSuite): {} accepted and read back to the canonical form, {} errors with the reference's code", rows, jts, ok, errs);
}
