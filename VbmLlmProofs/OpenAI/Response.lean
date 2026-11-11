import VbmLlm.OpenAI.Response
import VbmLlmProofs.Wire
import LeanJsonProofs.Fast
/-! # Proofs about the OpenAI chat-completions response decoder

Each theorem is a clause of the contract (`VbmLlm/OpenAI/Response.lean`, the header), stated of the decoder that runs. `*_ok_iff` says exactly what a value must be for a decode to succeed, and what it yields;
the refusals name the fault (path and kind). -/
namespace VbmLlm.OpenAI
open LeanJson

/-! ### Field readers -/

theorem optStr_ok_iff (o : Value) (k : String) (r : Option String) :
    optStr o k = .ok r ↔ (get o k = .null ∧ r = none) ∨ ∃ s, get o k = .str s ∧ r = some s := by
  unfold optStr; cases get o k <;> simp [eq_comm]

theorem optStr_wrong (o : Value) (k : String) (h : ∀ s, get o k ≠ .str s) (h' : get o k ≠ .null) :
    optStr o k = .error { path := [.key k], kind := .wrongType .string } := by
  unfold optStr; cases h2 : get o k <;> simp_all

theorem optNat_ok_iff (o : Value) (k : String) (r : Option Nat) :
    optNat o k = .ok r ↔ (get o k = .null ∧ r = none) ∨ ∃ n m, get o k = .num n ∧ natOf n = some m ∧ r = some m := by
  unfold optNat; cases get o k <;> simp [eq_comm]
  rename_i n; cases natOf n <;> simp [eq_comm]

theorem optNat_wrong (o : Value) (k : String) (h : ∀ n m, get o k = .num n → natOf n ≠ some m) (h' : get o k ≠ .null) :
    optNat o k = .error { path := [.key k], kind := .wrongType .natural } := by
  unfold optNat; cases h2 : get o k <;> simp_all
  rename_i n; cases h3 : natOf n <;> simp_all


theorem reqStr_ok_iff (o : Value) (k s : String) : reqStr o k = .ok s ↔ get o k = .str s := by
  unfold reqStr; cases get o k <;> simp [eq_comm]

theorem reqStr_missing (o : Value) (k : String) (h : get o k = .null) : reqStr o k = .error { path := [.key k], kind := .missing } := by
  simp [reqStr, h]

theorem reqStr_wrong (o : Value) (k : String) (h : ∀ s, get o k ≠ .str s) (h' : get o k ≠ .null) :
    reqStr o k = .error { path := [.key k], kind := .wrongType .string } := by
  unfold reqStr; cases h2 : get o k <;> simp_all

theorem reqObj_ok_iff (o : Value) (k : String) (w : Value) : reqObj o k = .ok w ↔ ∃ ms, get o k = .obj ms ∧ w = .obj ms := by
  unfold reqObj; cases get o k <;> simp [eq_comm]

theorem reqObj_missing (o : Value) (k : String) (h : get o k = .null) : reqObj o k = .error { path := [.key k], kind := .missing } := by
  simp [reqObj, h]

theorem reqObj_wrong (o : Value) (k : String) (h : ∀ ms, get o k ≠ .obj ms) (h' : get o k ≠ .null) :
    reqObj o k = .error { path := [.key k], kind := .wrongType .object } := by
  unfold reqObj; cases h2 : get o k <;> simp_all

theorem underStep_ok {α : Type} (s : Step) (e : Except Fault α) (a : α) : underStep s e = .ok a ↔ e = .ok a := by
  cases e <;> simp [underStep]

theorem underStep_error {α : Type} (s : Step) (e : Except Fault α) (f : Fault) : underStep s e = .error f ↔ ∃ g, e = .error g ∧ f = g.under s := by
  cases e <;> simp [underStep, eq_comm]

theorem optDetail_ok_iff (u : Value) (obj k : String) (r : Option Nat) :
    optDetail u obj k = .ok r ↔ (get u obj = .null ∧ r = none) ∨ ∃ ms, get u obj = .obj ms ∧ optNat (.obj ms) k = .ok r := by
  unfold optDetail; cases get u obj <;> simp [eq_comm]
  rename_i ms; rw [eq_comm, underStep_ok, eq_comm]


theorem bind_ok_iff {α β : Type} (x : Except Fault α) (f : α → Except Fault β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem pure_ok_iff {α : Type} (a b : α) : (pure a : Except Fault α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-! ### Tool calls (`ChatCompletionMessageToolCall`) -/

theorem checkType_ok_iff (v : Value) : checkType v = .ok () ↔ get v "type" = .null ∨ get v "type" = .str "function" := by
  unfold checkType; cases h : get v "type" <;> simp
  rename_i t; by_cases ht : t = "function" <;> simp [ht]

theorem checkType_ok_iff' (v : Value) (a : Unit) : checkType v = .ok a ↔ get v "type" = .null ∨ get v "type" = .str "function" := by
  cases a; exact checkType_ok_iff v

/-- A `type` that is a string other than `"function"` (a `custom` call, say) is refused as unsupported: it is not read as a function call. -/
theorem checkType_unsupported (v : Value) (t : String) (h : get v "type" = .str t) (ht : t ≠ "function") :
    checkType v = .error { path := [.key "type"], kind := .unsupported t } := by
  simp [checkType, h]

/-- **A tool call decodes exactly when** it is an object whose `type` is absent or `"function"`, with a string `id` and a `function` object holding string `name` and `arguments`;
it yields those strings, the arguments verbatim. -/
theorem decodeToolCall_ok_iff (v : Value) (c : ToolCall) :
    decodeToolCall v = .ok c ↔
      (∃ ms, v = .obj ms) ∧ (get v "type" = .null ∨ get v "type" = .str "function") ∧ get v "id" = .str c.id ∧
      ∃ fms, get v "function" = .obj fms ∧ get (.obj fms) "name" = .str c.name ∧ get (.obj fms) "arguments" = .str c.arguments := by
  cases v with
  | obj ms =>
    cases c with
    | mk id name arguments =>
      simp only [decodeToolCall, bind_ok_iff, pure_ok_iff, underStep_ok, checkType_ok_iff', reqStr_ok_iff, reqObj_ok_iff]
      simp
      intro _
      constructor
      · rintro ⟨a, ha, a1, ⟨ms1, h1, rfl⟩, a2, h2, a3, h3, rfl, rfl, rfl⟩
        exact ⟨ha, ms1, h1, h2, h3⟩
      · rintro ⟨ha, fms, h1, h2, h3⟩
        exact ⟨id, ha, .obj fms, ⟨fms, h1, rfl⟩, name, h2, arguments, h3, rfl, rfl, rfl⟩
  | _ => simp [decodeToolCall]

/-- A tool call of another kind (a `custom` call) is refused, never read as a function call. -/
theorem decodeToolCall_custom_refused (v : Value) (t : String) (h : get v "type" = .str t) (ht : t ≠ "function") (c : ToolCall) :
    decodeToolCall v ≠ .ok c := by
  intro hc; rw [decodeToolCall_ok_iff] at hc
  rcases hc with ⟨_, hty, _⟩; rcases hty with hty | hty <;> rw [h] at hty <;> simp at hty; exact ht hty

/-- A tool call with no `function` object is refused. -/
theorem decodeToolCall_no_function_refused (v : Value) (h : ∀ ms, get v "function" ≠ .obj ms) (c : ToolCall) : decodeToolCall v ≠ .ok c := by
  intro hc; rw [decodeToolCall_ok_iff] at hc
  rcases hc with ⟨_, _, _, fms, hf, _⟩; exact h fms hf

/-- The calls of an array decode exactly when every call does, member by member (the index only names a fault). -/
theorem decodeToolCalls_ok_iff (xs : List Value) (i : Nat) (cs : List ToolCall) :
    decodeToolCalls xs i = .ok cs ↔ Each (fun v c => decodeToolCall v = .ok c) xs cs := by
  induction xs generalizing i cs with
  | nil => simp [decodeToolCalls, each_nil_iff, eq_comm]
  | cons v vs ih =>
    simp only [decodeToolCalls, bind_ok_iff, pure_ok_iff, underStep_ok, ih, each_cons_iff]
    constructor
    · rintro ⟨c, hc, cs', hcs, rfl⟩; exact ⟨c, cs', rfl, hc, hcs⟩
    · rintro ⟨c, cs', rfl, hc, hcs⟩; exact ⟨c, hc, cs', hcs, rfl⟩

theorem decodeCalls_ok_iff (m : Value) (cs : List ToolCall) :
    decodeCalls m = .ok cs ↔ (get m "tool_calls" = .null ∧ cs = []) ∨ ∃ xs, get m "tool_calls" = .arr xs ∧ Each (fun v c => decodeToolCall v = .ok c) xs cs := by
  unfold decodeCalls
  cases get m "tool_calls" with
  | arr xs => simp [underStep_ok, decodeToolCalls_ok_iff]
  | _ => simp [eq_comm]

/-! ### Messages and choices -/

/-- The reasoning text is `reasoning`, else `reasoning_content`; each, when present, is a string. -/
theorem optReasoning_ok_iff (o : Value) (r : Option String) :
    optReasoning o = .ok r ↔ ∃ a b, optStr o "reasoning" = .ok a ∧ optStr o "reasoning_content" = .ok b ∧ r = (match a with | some _ => a | none => b) := by
  simp only [optReasoning, bind_ok_iff, pure_ok_iff]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩; exact ⟨a, b, ha, hb, h.symm⟩
  · rintro ⟨a, b, ha, hb, h⟩; exact ⟨a, ha, b, hb, h.symm⟩

/-- A present `reasoning` or `reasoning_content` that is not a string is refused, never coerced. -/
theorem optReasoning_wrong (o : Value) (k : String) (hk : k = "reasoning" ∨ k = "reasoning_content") (h : ∀ s, get o k ≠ .str s) (h' : get o k ≠ .null) (r : Option String) :
    optReasoning o ≠ .ok r := by
  intro hc; rw [optReasoning_ok_iff] at hc
  obtain ⟨a, b, ha, hb, _⟩ := hc
  rcases hk with rfl | rfl
  · rw [optStr_wrong o _ h h'] at ha; cases ha
  · rw [optStr_wrong o _ h h'] at hb; cases hb

theorem decodeMessage_ok_iff (m : Value) (r : Message) :
    decodeMessage m = .ok r ↔ optStr m "content" = .ok r.content ∧ optStr m "refusal" = .ok r.refusal ∧ decodeCalls m = .ok r.toolCalls ∧
      optReasoning m = .ok r.reasoning := by
  cases r with
  | mk content refusal toolCalls reasoning =>
    simp only [decodeMessage, bind_ok_iff, pure_ok_iff]
    constructor
    · rintro ⟨a, ha, b, hb, c, hc, d, hd, h⟩; cases h; exact ⟨ha, hb, hc, hd⟩
    · rintro ⟨ha, hb, hc, hd⟩; exact ⟨_, ha, _, hb, _, hc, _, hd, rfl⟩

theorem decodeChoice_ok_iff (c : Value) (r : Choice) :
    decodeChoice c = .ok r ↔ (∃ ms, c = .obj ms) ∧ optNat c "index" = .ok r.index ∧ optStr c "finish_reason" = .ok r.finishReason ∧
      ∃ ms, get c "message" = .obj ms ∧ decodeMessage (.obj ms) = .ok r.message := by
  cases c with
  | obj cms =>
    cases r with
    | mk index message finishReason =>
      simp only [decodeChoice, bind_ok_iff, pure_ok_iff, underStep_ok, reqObj_ok_iff]
      constructor
      · rintro ⟨a, ha, b, hb, m, ⟨ms, hm, rfl⟩, msg, hmsg, h⟩; cases h; exact ⟨⟨_, rfl⟩, ha, hb, ms, hm, hmsg⟩
      · rintro ⟨_, ha, hb, ms, hm, hmsg⟩; exact ⟨_, ha, _, hb, _, ⟨ms, hm, rfl⟩, _, hmsg, rfl⟩
  | _ => simp [decodeChoice]

/-- A choice with no `message` object is refused. -/
theorem decodeChoice_no_message_refused (c : Value) (h : ∀ ms, get c "message" ≠ .obj ms) (r : Choice) : decodeChoice c ≠ .ok r := by
  intro hc; rw [decodeChoice_ok_iff] at hc
  rcases hc with ⟨_, _, _, ms, hm, _⟩; exact h ms hm

theorem decodeChoices_ok_iff (xs : List Value) (i : Nat) (cs : List Choice) :
    decodeChoices xs i = .ok cs ↔ Each (fun v c => decodeChoice v = .ok c) xs cs := by
  induction xs generalizing i cs with
  | nil => simp [decodeChoices, each_nil_iff, eq_comm]
  | cons v vs ih =>
    simp only [decodeChoices, bind_ok_iff, pure_ok_iff, underStep_ok, ih, each_cons_iff]
    constructor
    · rintro ⟨c, hc, cs', hcs, rfl⟩; exact ⟨c, cs', rfl, hc, hcs⟩
    · rintro ⟨c, cs', rfl, hc, hcs⟩; exact ⟨c, hc, cs', hcs, rfl⟩

/-! ### Usage (`CompletionUsage`) -/

theorem decodeUsage_ok_iff (u : Value) (r : Usage) :
    decodeUsage u = .ok r ↔ optNat u "prompt_tokens" = .ok r.promptTokens ∧ optNat u "completion_tokens" = .ok r.completionTokens ∧ optNat u "total_tokens" = .ok r.totalTokens ∧
      optDetail u "prompt_tokens_details" "cached_tokens" = .ok r.cachedTokens ∧ optDetail u "completion_tokens_details" "reasoning_tokens" = .ok r.reasoningTokens ∧
      optCost u = .ok r.cost := by
  cases r with
  | mk p c t ca re co =>
    simp only [decodeUsage, bind_ok_iff, pure_ok_iff]
    constructor
    · rintro ⟨a, ha, b, hb, d, hd, e, he, f, hf, g, hg, h⟩; cases h; exact ⟨ha, hb, hd, he, hf, hg⟩
    · rintro ⟨ha, hb, hd, he, hf, hg⟩; exact ⟨_, ha, _, hb, _, hd, _, he, _, hf, _, hg, rfl⟩

/-! ### The reported cost (`usage.cost`)

The lexeme `1.68e-05`, the shape a small price is written in — as the pinned parser reads it from those bytes (`costLexeme_bytes`), so the brief's example is checked on the real text and not only on a
hand-built value — and the usage objects around it: with the cost, without it, with a minus sign, with one that is not a number. The `-0` case has a theorem of its own (`optCost_negZero`): it is zero and
it is refused, because the reader decides on the sign flag of the lexeme. -/

/-- `1.68e-05` as a number lexeme: no sign, the integer part `1` (`.nz 0 []`: the digit `0 + 1` and no more digits, the way `.nz 0 []` reads `1` elsewhere in this file), the fraction `.68`, the exponent
`e-05`. -/
def costLexeme : Number := ⟨false, .nz 0 [], some (6, [8]), some (true, 0, [5])⟩

/-- **The lexeme above is what the pinned parser reads from the provider's own bytes**: `1.68e-05` as text, through `LeanJson.parseFast`. (The reference parser is `rfl` on the byte list and the fast
parser is proved equal to it on every input, `LeanJsonProofs.parseFast_list`, so this is a decision procedure on the two, not a guess at the encoding.) -/
theorem costLexeme_bytes : LeanJson.parseFast "1.68e-05".toUTF8 = .ok (.num costLexeme) := by
  have h : "1.68e-05".toUTF8 = ⟨([0x31, 0x2E, 0x36, 0x38, 0x65, 0x2D, 0x30, 0x35] : List UInt8).toArray⟩ := by decide
  rw [h, LeanJson.parseFast_list]
  rfl

/-- `-0` as a number lexeme: the parser keeps the sign flag and the value zero. -/
def negZeroLexeme : Number := ⟨true, .zero, none, none⟩

/-- **`-0` is the lexeme with the sign flag set and the value zero**, as the pinned parser reads it from the bytes: what it writes is zero (`writesZero_negZero`), so it is not a number below zero. -/
theorem negZeroLexeme_bytes : LeanJson.parseFast "-0".toUTF8 = .ok (.num negZeroLexeme) := by
  have h : "-0".toUTF8 = ⟨([0x2D, 0x30] : List UInt8).toArray⟩ := by decide
  rw [h, LeanJson.parseFast_list]
  rfl

/-- A usage object with a numeric cost and every count. -/
def usageWithCost : Value :=
  .obj [("prompt_tokens", .num ⟨false, .nz 0 [], none, none⟩), ("completion_tokens", .num ⟨false, .nz 1 [], none, none⟩),
        ("total_tokens", .num ⟨false, .nz 0 [], none, none⟩), ("cost", .num costLexeme)]

/-- A usage object with the same counts and no cost. -/
def usageNoCost : Value :=
  .obj [("prompt_tokens", .num ⟨false, .nz 0 [], none, none⟩), ("completion_tokens", .num ⟨false, .nz 1 [], none, none⟩),
        ("total_tokens", .num ⟨false, .nz 0 [], none, none⟩)]

/-- The usage object of a cost written with a minus sign (`-0.0001`). -/
def usageNegativeCost : Value :=
  .obj [("prompt_tokens", .num ⟨false, .nz 0 [], none, none⟩), ("cost", .num ⟨true, .zero, some (0, [0, 0, 0, 1]), none⟩)]

/-- The usage object of a cost that is not a number (the string `"0.0001"`). -/
def usageStringCost : Value :=
  .obj [("prompt_tokens", .num ⟨false, .nz 0 [], none, none⟩), ("cost", .str "0.0001")]

/-- **What the amount reader accepts, exactly**: a lexeme written without a minus sign, read as itself; nothing else. The condition is `n.neg = false`, the sign flag of the lexeme: it is not a
statement about the value (a `-0` is zero and carries the flag). -/
theorem amountMember_ok_iff (n : Amount) (r : Option Amount) : amountMember n = .ok r ↔ n.neg = false ∧ r = some n := by
  unfold amountMember
  by_cases hn : n.neg = true
  · simp [hn]
  · have hf : n.neg = false := by simpa using hn
    simp only [hn, Bool.false_eq_true, ite_false, true_and]
    exact ⟨fun hr => (Except.ok.inj hr).symm, fun hr => by rw [hr]⟩

/-- **What the cost reader accepts, exactly**: no `cost` (absent or `null`) is no report, and a `cost` is read only when its lexeme is written without a minus sign -- a whole number, a fraction or an
exponent all are -- and it yields that lexeme itself, the number the provider wrote. "Written without a minus sign" is the sign flag (`n.neg = false`), not the value. -/
theorem optCostOf_ok_iff (o : Value) (r : Option Amount) :
    optCostOf o = .ok r ↔ (get o "cost" = .null ∧ r = none) ∨ ∃ n, get o "cost" = .num n ∧ n.neg = false ∧ r = some n := by
  unfold optCostOf
  cases h : get o "cost" with
  | null => exact ⟨fun hr => Or.inl ⟨rfl, (Except.ok.inj hr).symm⟩, fun hr => by rcases hr with ⟨-, rfl⟩ | ⟨n, hn, -⟩ <;> (first | rfl | cases hn)⟩
  | num n =>
    rw [amountMember_ok_iff]
    exact ⟨fun hr => Or.inr ⟨n, rfl, hr.1, hr.2⟩, fun hr => by
      rcases hr with ⟨hg, -⟩ | ⟨n1, hn, hf, hr⟩
      · cases hg
      · cases hn; exact ⟨hf, hr⟩⟩
  | bool b =>
    constructor
    · intro hr; cases hr
    · rintro (⟨hg, -⟩ | ⟨n, hn, -⟩)
      · cases hg
      · cases hn
  | str s =>
    constructor
    · intro hr; cases hr
    · rintro (⟨hg, -⟩ | ⟨n, hn, -⟩)
      · cases hg
      · cases hn
  | arr xs =>
    constructor
    · intro hr; cases hr
    · rintro (⟨hg, -⟩ | ⟨n, hn, -⟩)
      · cases hg
      · cases hn
  | obj ms =>
    constructor
    · intro hr; cases hr
    · rintro (⟨hg, -⟩ | ⟨n, hn, -⟩)
      · cases hg
      · cases hn

/-- (a) **The usage object `usageWithCost` decodes with that number as its `cost`**, and its counts are the counts (b) reads off `usageNoCost` (the same object without a cost). -/
theorem decodeUsage_cost_some :
    decodeUsage usageWithCost = .ok ⟨some 1, some 2, some 1, none, none, some costLexeme⟩ := by
  unfold decodeUsage optCost optCostOf amountMember optNat optDetail get lookup go usageWithCost costLexeme natOf digitsVal underStep Fault.under Fault.here
  rfl

/-- (b) **The usage object `usageNoCost` decodes with `cost = none`**, and its counts are those (a) reads off `usageWithCost`. -/
theorem decodeUsage_cost_none :
    decodeUsage usageNoCost = .ok ⟨some 1, some 2, some 1, none, none, none⟩ := by
  unfold decodeUsage optCost optCostOf amountMember optNat optDetail get lookup go usageNoCost natOf digitsVal underStep Fault.under Fault.here
  rfl

/-- (c) **A `cost` written with a minus sign is refused**, at `cost`, typed `negative`: never repaired, never read as 0. The reader decides on the lexeme's sign flag, so this theorem says "a minus
sign is refused"; it does not say the value is below zero (a `-0` is refused too, and it is zero: `optCost_negZero`). -/
theorem optCost_negative : optCost usageNegativeCost = .error { path := [.key "cost"], kind := .negative } := by
  unfold optCost usageNegativeCost optCostOf amountMember get lookup go underStep Fault.under Fault.here
  rfl

/-- (c) **A `cost` that is not a number is refused**, at `cost`, as not a number: never coerced. -/
theorem optCost_string : optCost usageStringCost = .error { path := [.key "cost"], kind := .wrongType .number } := by
  unfold optCost usageStringCost optCostOf get lookup go underStep Fault.under Fault.here
  rfl

/-- (c) The refusal reaches the usage decode: no `Usage` is decoded from the object whose `cost` is written with a minus sign. -/
theorem decodeUsage_negative_cost (r : Usage) : decodeUsage usageNegativeCost ≠ .ok r := by
  intro hc
  rw [decodeUsage_ok_iff] at hc
  obtain ⟨_, _, _, _, _, hcost⟩ := hc
  rw [optCost_negative] at hcost
  cases hcost

/-- (c) And so does the refusal of a `cost` that is not a number. -/
theorem decodeUsage_string_cost (r : Usage) : decodeUsage usageStringCost ≠ .ok r := by
  intro hc
  rw [decodeUsage_ok_iff] at hc
  obtain ⟨_, _, _, _, _, hcost⟩ := hc
  rw [optCost_string] at hcost
  cases hcost

/-- A reply with a usage report has that report's cost as its own: the accessor a caller reads. -/
theorem cost_some (r : Response) (u : Usage) (h : r.usage = some u) : r.cost = u.cost := by
  unfold Response.cost; rw [h]; rfl

/-- A reply with no usage report has no cost. -/
theorem cost_none (r : Response) (h : r.usage = none) : r.cost = none := by
  unfold Response.cost; rw [h]; rfl

/-- The lexeme writes the number zero: the integer part is `0` and every fraction digit is `0`. The property the fault's wording is about — `-0`, `-0.0` and `-0e5` all write zero, and none of them
is "below zero". (Its exponent is not read: the definition says what the digits write, and the theorems below name the three shapes.) -/
def writesZero (n : Number) : Prop :=
  n.int = .zero ∧ ∀ d ∈ (match n.frac with | none => [] | some (a, bs) => a :: bs), d.val = 0

/-- `-0` writes zero: its integer part is `0` and it has no fraction digit. -/
theorem writesZero_negZero : writesZero negZeroLexeme := ⟨rfl, by simp [negZeroLexeme]⟩

/-- `-0.0` writes zero too. -/
theorem writesZero_negZeroDot : writesZero ⟨true, .zero, some (0, []), none⟩ := ⟨rfl, by simp⟩

/-- And so does `-0e5`. -/
theorem writesZero_negZeroExp : writesZero ⟨true, .zero, none, some (false, 5, [])⟩ := ⟨rfl, by simp⟩

/-- `-0.0` as the pinned parser reads it from the bytes (the sign flag and the value zero, as `-0` is). -/
theorem negZeroDot_bytes : LeanJson.parseFast "-0.0".toUTF8 = .ok (.num ⟨true, .zero, some (0, []), none⟩) := by
  have h : "-0.0".toUTF8 = ⟨([0x2D, 0x30, 0x2E, 0x30] : List UInt8).toArray⟩ := by decide
  rw [h, LeanJson.parseFast_list]; rfl

/-- `-0e5` as the pinned parser reads it: the value is still zero, and the exponent does not make it negative. -/
theorem negZeroExp_bytes : LeanJson.parseFast "-0e5".toUTF8 = .ok (.num ⟨true, .zero, none, some (false, 5, [])⟩) := by
  have h : "-0e5".toUTF8 = ⟨([0x2D, 0x30, 0x65, 0x35] : List UInt8).toArray⟩ := by decide
  rw [h, LeanJson.parseFast_list]; rfl

/-- **`-0.0` is refused too**, for its sign: the same refusal as `-0`. -/
theorem optCost_negZeroDot : optCost (.obj [("cost", .num ⟨true, .zero, some (0, []), none⟩)]) =
    .error { path := [.key "cost"], kind := .negative } := by
  unfold optCost optCostOf amountMember get lookup go underStep Fault.under Fault.here
  rfl

/-- **And `-0e5`**: the exponent does not make zero negative, and the sign is still refused. (The three zeros written with a minus sign — `-0`, `-0.0`, `-0e5` — all write zero and all are refused for
the sign, which is what the fault kind and its text say.) -/
theorem optCost_negZeroExp : optCost (.obj [("cost", .num ⟨true, .zero, none, some (false, 5, [])⟩)]) =
    .error { path := [.key "cost"], kind := .negative } := by
  unfold optCost optCostOf amountMember get lookup go underStep Fault.under Fault.here
  rfl

/-- A lexeme whose sign flag is set is refused, whatever its value: this is the reader's rule, and the value never enters it. -/
theorem amountMember_neg (n : Amount) (h : n.neg = true) (r : Option Amount) : amountMember n ≠ .ok r := by
  intro hc; rw [amountMember_ok_iff] at hc; rw [h] at hc; cases hc.1

/-- The usage object of the cost `-0`: a zero written with a minus sign. -/
def usageNegZeroCost : Value :=
  .obj [("prompt_tokens", .num ⟨false, .nz 0 [], none, none⟩), ("cost", .num negZeroLexeme)]

/-- **A `-0` cost is refused**: not because a value is below zero (the lexeme's integer part is `.zero` and it has no fraction or exponent, so what it writes is zero: `negZeroLexeme`) but because it
is written with a minus sign. Decided on purpose: the library reads the provider's lexeme and never a float, so it refuses the sign rather than guessing that `-0` means `0`. -/
theorem optCost_negZero : optCost usageNegZeroCost = .error { path := [.key "cost"], kind := .negative } := by
  unfold optCost usageNegZeroCost optCostOf amountMember negZeroLexeme get lookup go underStep Fault.under Fault.here
  rfl

/-- And it reaches the usage decode: no `Usage` is decoded from an object whose `cost` is `-0`. -/
theorem decodeUsage_negZero_cost (r : Usage) : decodeUsage usageNegZeroCost ≠ .ok r := by
  intro hc
  rw [decodeUsage_ok_iff] at hc
  obtain ⟨_, _, _, _, _, hcost⟩ := hc
  rw [optCost_negZero] at hcost
  cases hcost

/-- A whole reply that reports the cost `1.68e-05`: an object with an `id`, one choice and a usage object. -/
def replyWithCost : Value :=
  .obj [("id", .str "x"), ("choices", .arr [.obj [("index", .num ⟨false, .zero, none, none⟩), ("message", .obj [("role", .str "assistant"), ("content", .str "hi")]), ("finish_reason", .str "stop")]]),
        ("usage", usageWithCost)]

/-- The same reply with no `cost` in its usage. -/
def replyNoCost : Value :=
  .obj [("id", .str "x"), ("choices", .arr [.obj [("index", .num ⟨false, .zero, none, none⟩), ("message", .obj [("role", .str "assistant"), ("content", .str "hi")]), ("finish_reason", .str "stop")]]),
        ("usage", usageNoCost)]

/-- **A whole reply decodes with the reported cost in its usage**: `decode` of a reply that carries `usage.cost` yields a `Response` with that usage. -/
theorem decode_reply_cost :
    decode replyWithCost = .ok ⟨some "x", none, [⟨some 0, ⟨some "hi", none, [], none⟩, some "stop"⟩],
      some ⟨some 1, some 2, some 1, none, none, some costLexeme⟩, none⟩ := by
  unfold decode decodeChoicesField decodeChoices decodeChoice decodeMessage decodeCalls decodeToolCalls
    optStr optNat optReasoning decodeUsageOpt decodeUsage optDetail optCost optCostOf amountMember reqObj
    replyWithCost usageWithCost get lookup go natOf digitsVal underStep Fault.under Fault.here
  rfl

/-- **The accessor a caller reads, on a decoded reply**: the cost of a whole reply comes off `decode` as the lexeme the provider wrote. This is the theorem that connects `Response.cost` to the decoder (it
was missing: the accessor had only its own two lemmas). -/
theorem decode_reply_cost_accessor : (decode replyWithCost).map Response.cost = .ok (some costLexeme) := by
  rw [decode_reply_cost]; rfl

/-- A whole reply that reports no cost decodes with `cost = none`: the other half of the same fact, on a decoded reply. -/
theorem decode_reply_noCost :
    decode replyNoCost = .ok ⟨some "x", none, [⟨some 0, ⟨some "hi", none, [], none⟩, some "stop"⟩],
      some ⟨some 1, some 2, some 1, none, none, none⟩, none⟩ := by
  unfold decode decodeChoicesField decodeChoices decodeChoice decodeMessage decodeCalls decodeToolCalls
    optStr optNat optReasoning decodeUsageOpt decodeUsage optDetail optCost optCostOf amountMember reqObj
    replyNoCost usageNoCost get lookup go natOf digitsVal underStep Fault.under Fault.here
  rfl

/-- The accessor on that decoded reply: no usage cost reported, no cost off the reply. -/
theorem decode_reply_noCost_accessor : (decode replyNoCost).map Response.cost = .ok none := by
  rw [decode_reply_noCost]; rfl

/-- `cost_some` applied to a concrete reply that has a usage report (its hypothesis holds), so the theorem is not vacuous; `decode_reply_cost_accessor` is the same fact for the reply `decode` returns. -/
theorem cost_some_witness :
    (⟨some "x", none, [], some ⟨some 1, some 2, some 1, none, none, some costLexeme⟩, none⟩ : Response).cost = some costLexeme := by
  rw [cost_some _ _ rfl]

/-- `cost_none` applied to a reply with no usage report: its hypothesis holds too. -/
theorem cost_none_witness : (⟨some "x", none, [], none, none⟩ : Response).cost = none :=
  cost_none _ rfl

theorem decodeUsageOpt_ok_iff (v : Value) (r : Option Usage) :
    decodeUsageOpt v = .ok r ↔ (get v "usage" = .null ∧ r = none) ∨ ∃ ms u, get v "usage" = .obj ms ∧ decodeUsage (.obj ms) = .ok u ∧ r = some u := by
  unfold decodeUsageOpt
  cases get v "usage" with
  | obj ms =>
    cases h : decodeUsage (.obj ms) <;> simp [underStep, h, Functor.map, Except.map]
    exact eq_comm
  | _ => simp [eq_comm]

/-! ### The reply -/

theorem decodeChoicesField_ok_iff (v : Value) (cs : List Choice) :
    decodeChoicesField v = .ok cs ↔ ∃ xs, get v "choices" = .arr xs ∧ xs ≠ [] ∧ Each (fun x c => decodeChoice x = .ok c) xs cs := by
  unfold decodeChoicesField
  cases get v "choices" with
  | arr xs => cases xs <;> simp [underStep_ok, decodeChoices_ok_iff]
  | _ => simp

/-- **The whole contract in one statement.** A value decodes to `r` exactly when it is an object, its optional `id`, `model` and `provider` are strings or absent, its `choices` is a non-empty array every member of which
decodes (to `r.choices`, member by member), and its `usage` is absent or decodes (to `r.usage`). -/
theorem decode_ok_iff (v : Value) (r : Response) :
    decode v = .ok r ↔
      (∃ ms, v = .obj ms) ∧ optStr v "id" = .ok r.id ∧ optStr v "model" = .ok r.model ∧
      (∃ xs, get v "choices" = .arr xs ∧ xs ≠ [] ∧ Each (fun x c => decodeChoice x = .ok c) xs r.choices) ∧ decodeUsageOpt v = .ok r.usage ∧
      optStr v "provider" = .ok r.provider := by
  cases v with
  | obj ms =>
    cases r with
    | mk id model choices usage provider =>
      simp only [decode, bind_ok_iff, pure_ok_iff, decodeChoicesField_ok_iff]
      constructor
      · rintro ⟨a, ha, b, hb, c, hc, d, hd, e, he, h⟩; cases h; exact ⟨⟨_, rfl⟩, ha, hb, hc, hd, he⟩
      · rintro ⟨_, ha, hb, hc, hd, he⟩; exact ⟨_, ha, _, hb, _, hc, _, hd, _, he, rfl⟩
  | _ => simp [decode]

/-- A reply that is not an object is refused. -/
theorem decode_not_object (v : Value) (h : ∀ ms, v ≠ .obj ms) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; rcases hc with ⟨⟨ms, hms⟩, _⟩; exact h ms hms

/-- A reply with no `choices` is refused (nothing to read), and so is one whose `choices` is empty. -/
theorem decode_no_choices (v : Value) (h : get v "choices" = .null) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; rcases hc with ⟨_, _, _, ⟨xs, hx, _⟩, _⟩; rw [h] at hx; cases hx

theorem decode_empty_choices (v : Value) (h : get v "choices" = .arr []) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; rcases hc with ⟨_, _, _, ⟨xs, hx, hne, _⟩, _⟩; rw [h] at hx; cases hx; exact hne rfl

/-- A reply whose `choices` is not an array is refused. -/
theorem decode_choices_not_array (v : Value) (h : ∀ xs, get v "choices" ≠ .arr xs) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; rcases hc with ⟨_, _, _, ⟨xs, hx, _⟩, _⟩; exact h xs hx

/-- A well-typed reply is **never coerced**: a present `id` that is not a string is refused. -/
theorem decode_id_wrong_type (v : Value) (h : ∀ s, get v "id" ≠ .str s) (h' : get v "id" ≠ .null) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; rcases hc with ⟨_, hid, _⟩; rw [optStr_wrong v "id" h h'] at hid; cases hid

/-- A present `provider` that is not a string is refused. -/
theorem decode_provider_wrong_type (v : Value) (h : ∀ s, get v "provider" ≠ .str s) (h' : get v "provider" ≠ .null) (r : Response) : decode v ≠ .ok r := by
  intro hc; rw [decode_ok_iff] at hc; rcases hc with ⟨_, _, _, _, _, hp⟩; rw [optStr_wrong v "provider" h h'] at hp; cases hp

end VbmLlm.OpenAI
