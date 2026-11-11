import LeanJsonProofs.Grammar
import LeanJsonProofs.Print
import LeanJsonProofs.PrintBytes
import LeanJsonProofs.PrintTape
import LeanJsonProofs.PrintSimd
import LeanJsonProofs.Policy
import LeanJsonProofs.Fast
import LeanJsonProofs.FastLoop
import LeanJsonProofs.Stage1
import LeanJsonProofs.ParseC
/-! # The obligation ledger

Every claim the library makes, keyed by a slug. A claim is `proved` only by naming theorems (double-backtick names are checked at
elaboration, so a renamed or deleted theorem breaks this file), `partly` when theorems cover only a part (the note says which part is open),
`open_` when nothing is proved, or `limit` when no machine decides it (the note says who carries it).
`scripts/LedgerGate.lean` renders `docs/proof-ledger.md` from this list and ratchets it: proved may only rise, open may only fall. A report
may not call anything verified that is not `proved`. The claims are the plan's (docs/decisions/0001-vbm-json.md); at scaffolding
every one is open. -/

inductive Status where
  | proved (thms : List Lean.Name)
  | partly (thms : List Lean.Name) (open_ : String)
  | open_ (note : String)
  | limit (carriedBy : String)

structure Obligation where
  slug   : String
  status : Status

def O (slug : String) (s : Status) : Obligation := ⟨slug, s⟩

def ledger : List Obligation := [
  -- the grammar and the reference
  O "grammar-is-rfc8259" (.limit "the grammar relation is written from the ABNF of RFC 8259; checked by review against the RFC (no machine decides fidelity to a prose standard)"),
  O "grammar-is-unambiguous" (.partly [``LeanJson.json_unique] "the grammar relates a byte string to at most one value (proved of the relation, through the reference). Open: derivation trees are not claimed unique (the fast parser returns the same value as the reference, `parseFast_eq_parse`, so the statement holds of what the exports run)"),
  O "reference-recogniser-is-sound-and-complete" (.proved [``LeanJson.parse_ok_iff, ``LeanJson.parse_error_iff, ``LeanJson.parseFast_ok_iff, ``LeanJson.parseFast_error_iff]),
  -- parse and print
  O "parse-is-total" (.proved [``LeanJson.parse_total, ``LeanJson.parseFast_total]),
  O "parse-is-sound" (.proved [``LeanJson.parse_sound, ``LeanJson.parseFast_sound]),
  O "parse-is-complete" (.proved [``LeanJson.parse_complete, ``LeanJson.parseFast_complete]),
  O "print-parse-round-trip" (.partly [``LeanJson.print_roundtrip, ``LeanJson.print_canonical, ``LeanJson.parseFast_print] "parse (print v) = v for every value within maxDepth (a value deeper than maxDepth is printed and then refused with the depth code, so the unconditional statement is false by policy); print then parse then print is stable. Proved of the reference, the printer and the fast parser (`parseFast_print`); the exports print the tape (`printTape`, `LeanJson/PrintTape.lean`) and the encoder's tape of a value prints to `print v` (`printTape_encode`, claim `print-tape-prints-the-value`), the byte printer `printBytes` is equal to `print` (`print-bytes-equal-reference-printer`). Open: that the printer is total on every tape the parser writes without the size bound (the format's sizes: below 2^50 words and text bytes), which no machine ever reaches"),
  O "print-output-is-accepted" (.partly [``LeanJson.print_json] "print's output is derivable in the grammar, for every value. Proved of the printer and the grammar; the export prints a tape: for the tape of a value it is `print v` (`printTape_encode`), so derivable; for a forged tape, derivability of what it prints (its strings are checked UTF-8 and its numbers checked lexemes) is tested (`tests/abi_test.c`: forged tapes are refused or print a document that parses), not proved"),
  O "print-bytes-equal-reference-printer" (.proved [``LeanJson.printBytes_eq, ``LeanJson.escapeString_eq, ``LeanJson.pushString_eq, ``LeanJson.pushNumber_eq]),
  O "print-tape-prints-the-value" (.partly [``LeanJson.printTape_encode, ``LeanJsonProofs.printTapeS_eq, ``LeanJson.escapeChecked_eq, ``LeanJsonProofs.escapeCheckedS_eq, ``LeanJson.numLex_complete, ``LeanJson.utf8Range_complete, ``LeanJson.escLoopR_eq, ``LeanJson.pleaf_eq, ``LeanJsonProofs.pleafS_eq] "`vbm_json_print_tape` runs `printTapeS` (`printTapeS_eq`: it is `printTape`, the same printer with the words read by one `ld64` and the texts a word at a time): for the tape the encoder writes for a value within `maxDepth` and the format's sizes, it is `print v` (`printTape_encode`); `vbm_json_escape_string` runs `escapeCheckedS` (`escapeCheckedS_eq`: it is `escapeChecked`, a word at a time): for the UTF-8 of a string, the literal `printString` (`escapeChecked_eq`). Open: refusal of every forged tape and of every non-UTF-8 text is not proved (soundness of the checks: the rows of `tests/abi_test.c` test it, with an independent UTF-8 decoder and escape table)"),
  O "print-reproduces-lean-compress" (.limit "byte equality with Lean.Json.compress is a one-time differential run on the corpus (the consumer's journal hash chains cover bytes), deleted after migration"),
  -- the fast parser
  O "fast-parser-refines-reference" (.proved [``LeanJson.parseFast_eq_parse]),
  O "fast-parser-terminates-in-bounded-space" (.open_ "the loop `run` is total (structural recursion on its fuel, and `run_sound` shows the fuel a.size + 2 is enough) and is a self tail call (the emitted C is a loop: `goto _start`, checked by reading the C, not proved); the explicit stack's depth is bounded by maxDepth by the budget `d`, which is NOT proved as a separate invariant (only its consequence: an accepted value has depth at most maxDepth, `parseFast_sound`)"),
  -- the bit-parallel parser (docs/perf/simd-plan.md): the export `vbm_json_parse_tape` is `parseTapeSimd`, which these claims are about (stage 1 and the index-driven loop `runW`); the scalar parser is its fallback
  O "simd-structural-stage-is-the-byte-machine" (.proved [``LeanJsonProofs.stage1_spec, ``LeanJsonProofs.stage1_stream]),
  O "simd-parser-equals-scalar-parser" (.proved [``LeanJsonProofs.parseTapeSimd_eq]),
  -- the policies (PROPOSED, owner ratification pending: docs/decisions/0001-vbm-json.md)
  O "policy-no-lone-surrogates-no-invalid-utf8" (.partly [``LeanJson.utf8_scalar, ``LeanJson.esc_scalar, ``LeanJson.chars_scalar, ``LeanJson.lone_high_surrogate_rejected, ``LeanJson.lone_low_surrogate_rejected, ``LeanJson.overlong_utf8_rejected, ``LeanJson.utf8_surrogate_rejected, ``LeanJson.surrogate_pair_is_one_scalar, ``LeanJson.parseFast_lone_high_surrogate_rejected, ``LeanJson.parseFast_lone_low_surrogate_rejected, ``LeanJson.parseFast_overlong_utf8_rejected, ``LeanJson.parseFast_utf8_surrogate_rejected, ``LeanJson.parseFast_surrogate_pair_is_one_scalar] "strict: both rejected (RFC 8259 permits either; I-JSON forbids). Proved of the grammar relation: every derived scalar is a Unicode scalar value; and of the fast parser, by `parseFast_eq_parse`: the named inputs are rejected and a surrogate pair is one scalar. Open: a general theorem over every input with a lone surrogate or invalid UTF-8 (the examples and the grammar carry it; the differential and the exhaustive vectors test it)"),
  O "policy-numbers-are-lexemes" (.partly [``LeanJson.number_is_a_lexeme, ``LeanJson.leading_zero_rejected, ``LeanJson.parseFast_number_is_a_lexeme, ``LeanJson.parseFast_leading_zero_rejected] "numbers kept as sign, digits, exponent lexemes; no floats in the core. Checked by the type (Number) and by examples of the reference and of the fast parser"),
  O "policy-duplicate-keys-kept-in-order" (.partly [``LeanJson.duplicate_keys_kept_in_order, ``LeanJson.parseFast_duplicate_keys_kept_in_order] "duplicate object keys are kept, in input order. Examples of the reference and of the fast parser; the type (a list of pairs) and parseFast_ok_iff carry the general case"),
  O "policy-max-depth-is-an-error-code" (.partly [``LeanJson.depth_at_limit_accepted, ``LeanJson.depth_past_limit_is_error_code, ``LeanJson.depth_error_comes_first, ``LeanJson.parseFast_depth_at_limit_accepted, ``LeanJson.parseFast_depth_past_limit_is_error_code, ``LeanJson.parseFast_depth_error_comes_first, ``LeanJson.depth_100000_is_error_code, ``LeanJson.parseFast_depth_100000_is_error_code, ``LeanJson.parse_too_deep, ``LeanJson.parseFast_too_deep] "nesting past maxDepth is reported as the named error code depth, never a crash. Examples of the reference and of the fast parser (the boundary, and the error reported before a later syntax error); the accept side is parseFast_ok_iff; the fast parser returns the reference's error code on every input (`parseFast_eq_parse`). A derivable text too deep is an error (`parse_too_deep`, `parseFast_too_deep`) and 100000 deep is the depth code, both proved; the vectors have 100000-deep rows and a no-bound mutant is shown caught. Open: that the code is exactly depth (not syntax) in general"),
  -- the ABI edge
  O "tape-encode-decode" (.partly [``LeanJson.encValue_layout, ``LeanJson.encValue_empty, ``LeanJson.closeNode_arr, ``LeanJson.closeNode_obj, ``LeanJson.parseTapeFast_eq, ``LeanJson.parseTapeFast_ok, ``LeanJson.parseTapeFast_error] "the tape the export `vbm_json_parse_tape` returns is, byte for byte, the layout of the reference's value (`parseTapeFast_ok`: `tapeOk (encValue v)`, with `encValue_layout`: the tape is a pure function of the value, header words, subtree sizes, text offsets) or the error words (`parseTapeFast_error`). One reader is proved: the printer `printTape` prints the value's tape to `print v` (`printTape_encode`). Open: the bindings' readers, a decoder from the tape back to the value and the theorem that it inverts the layout (the bindings' tape readers are tested against the reference, not proved)"),
  O "abi-buffers-need-no-allocator-across-the-boundary" (.limit "a property of the C edge (caller-owned buffers, needed-size return): tested by the shared vectors and the binding runners, not provable in Lean"),
  -- the bindings
  O "bindings-agree-with-the-reference" (.limit "every binding runs the shared vectors the Lean reference generated, in Tier 1; a second decoder per language is tested, not proved")]
