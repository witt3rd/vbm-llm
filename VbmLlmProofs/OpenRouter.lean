import VbmLlm.OpenRouter.ApiError
import VbmLlm.Finish
import VbmLlmProofs.OpenAI.Response
import VbmLlmProofs.Finish
/-! # Proofs about OpenRouter's deviations (`VbmLlm/OpenRouter/ApiError.lean`, `FinishClass.ofOpenRouter`)

* **The finish reason** (`ofOpenRouter_error`, `ofOpenRouter_other`): `error` is its own class (a generation that failed after it began); every other word is classed as OpenAI classes it.
* **The code of an error** (`optCode_*`, `decodeApiError_*`): a word or a plain natural, each as itself; a fraction or any other type is refused, never coerced. -/
namespace VbmLlm.OpenRouter
open VbmLlm OpenAI LeanJson

theorem _root_.VbmLlm.FinishClass.ofOpenRouter_error : FinishClass.ofOpenRouter "error" = .failed := rfl

/-- Every other word is classed exactly as OpenAI's. -/
theorem _root_.VbmLlm.FinishClass.ofOpenRouter_other (w : String) (h : w ≠ "error") : FinishClass.ofOpenRouter w = FinishClass.ofOpenAI w := by
  unfold FinishClass.ofOpenRouter; split <;> simp_all

theorem optCode_ok_iff (e : Value) (r : Option Code) :
    optCode e = .ok r ↔ (get e "code" = .null ∧ r = none) ∨ (∃ s, get e "code" = .str s ∧ r = some (.text s)) ∨ ∃ n m, get e "code" = .num n ∧ natOf n = some m ∧ r = some (.num m) := by
  unfold optCode; cases get e "code" <;> simp [eq_comm]
  rename_i n; cases natOf n <;> simp [eq_comm]

/-- A code that is a fraction, a sign or an exponent, or not a word or a number, is refused. -/
theorem optCode_wrong (e : Value) (h : ∀ s, get e "code" ≠ .str s) (hn : get e "code" ≠ .null) (hm : ∀ n m, get e "code" = .num n → natOf n ≠ some m) (r : Option Code) : optCode e ≠ .ok r := by
  intro hc; rw [optCode_ok_iff] at hc
  rcases hc with ⟨h1, _⟩ | ⟨s, h1, _⟩ | ⟨n, m, h1, h2, _⟩
  · exact hn h1
  · exact h s h1
  · exact hm n m h1 h2

theorem decodeApiError_ok_iff (v : Value) (r : ApiError) :
    decodeApiError v = .ok r ↔ (∃ ms, v = .obj ms) ∧ ∃ ems, get v "error" = .obj ems ∧ get (.obj ems) "message" = .str r.message ∧ optCode (.obj ems) = .ok r.code := by
  cases v with
  | obj ms =>
    cases r with
    | mk message code =>
      simp only [decodeApiError, bind_ok_iff, underStep_ok, reqObj_ok_iff]
      simp only [pure_ok_iff, reqStr_ok_iff]
      constructor
      · rintro ⟨e, ⟨ems, hems, rfl⟩, m, hm, c, hc, h⟩
        cases h; exact ⟨⟨_, rfl⟩, ems, hems, hm, hc⟩
      · rintro ⟨_, ems, hems, hm, hc⟩
        exact ⟨_, ⟨ems, hems, rfl⟩, _, hm, _, hc, rfl⟩
  | _ => simp [decodeApiError]

/-- A body that is not an object, or has no `error` object, or no string `message`, is refused. -/
theorem decodeApiError_not_object (v : Value) (h : ∀ ms, v ≠ .obj ms) (r : ApiError) : decodeApiError v ≠ .ok r := by
  intro hc; rw [decodeApiError_ok_iff] at hc; obtain ⟨⟨ms, hms⟩, _⟩ := hc; exact h ms hms

theorem decodeApiError_no_error (v : Value) (h : ∀ ms, get v "error" ≠ .obj ms) (r : ApiError) : decodeApiError v ≠ .ok r := by
  intro hc; rw [decodeApiError_ok_iff] at hc; obtain ⟨_, ems, hems, _⟩ := hc; exact h ems hems

theorem decodeApiError_no_message (v : Value) (ems : List (String × Value)) (h : get v "error" = .obj ems) (hm : ∀ s, get (.obj ems) "message" ≠ .str s) (r : ApiError) :
    decodeApiError v ≠ .ok r := by
  intro hc; rw [decodeApiError_ok_iff] at hc
  obtain ⟨_, ems', hems', hm', _⟩ := hc
  rw [h] at hems'; cases hems'; exact hm _ hm'

end VbmLlm.OpenRouter
