import VbmLlm.OpenAI.Render
import VbmLlmProofs.OpenAI.Response
/-! # Proofs about the rendering (`VbmLlm/OpenAI/Render.lean`)

The rendering is what the conformance vectors compare against (`vectors/`), so the one behaviour the reported cost could have disturbed is stated of it: **a usage report with no cost renders exactly
as it did before `cost` was read**, and a report with one gets the field, in the same place, as the lexeme the provider wrote. -/
namespace VbmLlm.OpenAI
open LeanJson

/-- **A usage report that carries no cost renders without a `cost` field**, on one concrete report (the empty one, every count unreported): the line is the one the library printed before the cost was read, so
no vector expectation of an uncosted reply moves. `render_cost_example` is the other case. This is one report, not every report: it is the case a reviewer compares with the expectations by hand, and
`lake exe vbm-llm-vectors --check` compares the rest on the recorded data. -/
theorem render_no_cost_example :
    (⟨none, none, none, none, none, none⟩ : Usage).render.toList =
      "usage prompt=none completion=none total=none cached=none reasoning=none\ntokens uncached=0 read=0 write=0 output=0 reasoning=0".toList := by
  set_option maxRecDepth 1000000 in
  decide

/-- **A usage report that carries a cost renders it**, on one concrete report: the field is added (only when there is one) and it shows the lexeme the provider wrote. -/
theorem render_cost_example :
    (⟨some 1, some 2, some 1, none, none, some costLexeme⟩ : Usage).render.toList =
      "usage prompt=1 completion=2 total=1 cached=none reasoning=none cost=1.68e-05\ntokens uncached=1 read=0 write=0 output=2 reasoning=0".toList := by
  set_option maxRecDepth 1000000 in
  decide


end VbmLlm.OpenAI
