/-! # The event interface of the stream fold (a stub of `vbm-sse`)

A convention's stream arrives as server-sent events. Splitting bytes into events is `vbm-sse`'s job (whole-buffer, then chunk-invariant); the fold of this library starts from the **events** it
produces, so the interface, not an implementation, is the contract: an event has a type (`""` when the stream names none), its data (consecutive `data` lines joined with LF) and an optional id.
Until `vbm-sse` exists and is pinned as a lake dependency like `vbm-json`, the conformance checker (`vectors/Main.lean`) carries a minimal splitter that stands in for it; nothing in `VbmLlm` does. -/
namespace VbmLlm

/-- One dispatched server-sent event. -/
structure Event where
  /-- the `event:` field, `""` when none was given -/
  type : String
  /-- the `data` lines of the event, joined with LF -/
  data : String
  /-- the `id:` field when one was given -/
  id : Option String
  deriving DecidableEq, Repr

end VbmLlm
