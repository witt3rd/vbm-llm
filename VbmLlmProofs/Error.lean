import VbmLlm.OpenAI.ApiError
import VbmLlm.Error
import VbmLlmProofs.OpenAI.Response
/-! # Proofs about the error taxonomy and the error body (`VbmLlm/Error.lean`, `VbmLlm/OpenAI/ApiError.lean`)

* **The class of a status** (`ofStatus_auth`, `_quota`, `_timeout`, `_rateLimit`, `_tls`, `_server`): 401 and 403 are `auth`, 402 `quota`, 408 `timeout`, 429 `rateLimit`, the two TLS statuses `invalid`, any other server error `overloaded`.
* **`overflow` is a client error whose words say so** (`ofStatus_overflow_iff`): never a server's, never from a status that names its own class, and never without the consumer's verdict (`ofStatus_no_words`).
* **The body of a failed call** (`decodeApiError_ok_iff`, and the refusals): read as the schema says, a wrong type refused, never coerced. -/
namespace VbmLlm
open OpenAI LeanJson

theorem ErrorClass.ofStatus_auth (w : Bool) : ErrorClass.ofStatus 401 w = .auth ∧ ErrorClass.ofStatus 403 w = .auth := by simp [ErrorClass.ofStatus]
theorem ErrorClass.ofStatus_quota (w : Bool) : ErrorClass.ofStatus 402 w = .quota := by simp [ErrorClass.ofStatus]
theorem ErrorClass.ofStatus_timeout (w : Bool) : ErrorClass.ofStatus 408 w = .timeout := by simp [ErrorClass.ofStatus]
theorem ErrorClass.ofStatus_rateLimit (w : Bool) : ErrorClass.ofStatus 429 w = .rateLimit := by simp [ErrorClass.ofStatus]
theorem ErrorClass.ofStatus_tls (w : Bool) : ErrorClass.ofStatus 525 w = .invalid ∧ ErrorClass.ofStatus 526 w = .invalid := by simp [ErrorClass.ofStatus]

/-- Any other server error is an overloaded provider, whatever the message says. -/
theorem ErrorClass.ofStatus_server (n : Nat) (w : Bool) (h : 500 ≤ n) (h5 : n ≠ 525) (h6 : n ≠ 526) : ErrorClass.ofStatus n w = .overloaded := by
  have : n ≠ 401 := by omega
  have : n ≠ 403 := by omega
  have : n ≠ 402 := by omega
  have : n ≠ 408 := by omega
  have : n ≠ 429 := by omega
  simp [ErrorClass.ofStatus, *]

/-- **`overflow` exactly when** the consumer's words say so and the status is a client error that names no class of its own. -/
theorem ErrorClass.ofStatus_overflow_iff (n : Nat) (w : Bool) :
    ErrorClass.ofStatus n w = .overflow ↔ w = true ∧ n < 500 ∧ n ≠ 401 ∧ n ≠ 402 ∧ n ≠ 403 ∧ n ≠ 408 ∧ n ≠ 429 := by
  unfold ErrorClass.ofStatus
  repeat' split
  all_goals simp_all <;> omega

/-- Without the consumer's verdict on the words, nothing is `overflow`. -/
theorem ErrorClass.ofStatus_no_words (n : Nat) : ErrorClass.ofStatus n false ≠ .overflow := by
  intro h; have := (ErrorClass.ofStatus_overflow_iff n false).1 h; simp at this

/-! ### The body of a failed call -/

theorem decodeApiError_ok_iff (v : Value) (r : ApiError) :
    decodeApiError v = .ok r ↔ (∃ ms, v = .obj ms) ∧
      ∃ ems, get v "error" = .obj ems ∧ get (.obj ems) "message" = .str r.message ∧ optStr (.obj ems) "type" = .ok r.type ∧
        optStr (.obj ems) "param" = .ok r.param ∧ optStr (.obj ems) "code" = .ok r.code := by
  cases v with
  | obj ms =>
    cases r with
    | mk message type param code =>
      simp only [decodeApiError, bind_ok_iff, underStep_ok, reqObj_ok_iff]
      simp only [pure_ok_iff, reqStr_ok_iff]
      constructor
      · rintro ⟨e, ⟨ems, hems, rfl⟩, m, hm, t, ht, p, hp, c, hc, h⟩
        cases h; exact ⟨⟨_, rfl⟩, ems, hems, hm, ht, hp, hc⟩
      · rintro ⟨_, ems, hems, hm, ht, hp, hc⟩
        exact ⟨_, ⟨ems, hems, rfl⟩, _, hm, _, ht, _, hp, _, hc, rfl⟩
  | _ => simp [decodeApiError]

/-- A body that is not an object is refused. -/
theorem decodeApiError_not_object (v : Value) (h : ∀ ms, v ≠ .obj ms) (r : ApiError) : decodeApiError v ≠ .ok r := by
  intro hc; rw [decodeApiError_ok_iff] at hc; obtain ⟨⟨ms, hms⟩, _⟩ := hc; exact h ms hms

/-- A body with no `error` object is refused. -/
theorem decodeApiError_no_error (v : Value) (h : ∀ ms, get v "error" ≠ .obj ms) (r : ApiError) : decodeApiError v ≠ .ok r := by
  intro hc; rw [decodeApiError_ok_iff] at hc; obtain ⟨_, ems, hems, _⟩ := hc; exact h ems hems

/-- An error with no string `message` is refused. -/
theorem decodeApiError_no_message (v : Value) (ems : List (String × Value)) (h : get v "error" = .obj ems) (hm : ∀ s, get (.obj ems) "message" ≠ .str s) (r : ApiError) :
    decodeApiError v ≠ .ok r := by
  intro hc; rw [decodeApiError_ok_iff] at hc
  obtain ⟨_, ems', hems', hm', _⟩ := hc
  rw [h] at hems'; cases hems'; exact hm _ hm'

/-- Nothing is coerced: a `code` that is present and not a string (a number, say) is refused. -/
theorem decodeApiError_code_wrong (v : Value) (ems : List (String × Value)) (h : get v "error" = .obj ems) (hc : ∀ s, get (.obj ems) "code" ≠ .str s)
    (hn : get (.obj ems) "code" ≠ .null) (r : ApiError) : decodeApiError v ≠ .ok r := by
  intro hd; rw [decodeApiError_ok_iff] at hd
  obtain ⟨_, ems', hems', _, _, _, hcode⟩ := hd
  rw [h] at hems'; cases hems'; rw [optStr_wrong _ _ hc hn] at hcode; cases hcode

end VbmLlm
