/-! # Typed refusals: where a reply is malformed, and how

A decoder never guesses. A reply that does not fit the convention is refused with a `Fault`: a **path** (the keys and indices from the root of the reply to the offending value, built on the way
out so a successful decode allocates none of it) and a **kind**. The kinds are a closed set; a consumer matches on them, and the text of `Fault.render` is for humans and carries nothing a consumer needs. -/
namespace VbmLlm

/-- One step of a path: an object key or an array index. -/
inductive Step where
  | key (k : String)
  | idx (i : Nat)
  deriving DecidableEq, Repr

/-- The JSON types a decoder expects. -/
inductive Ty where
  | object | array | string | natural | boolean | number
  deriving DecidableEq, Repr

/-- Why a value is refused. -/
inductive Kind where
  /-- a required value is absent or `null` -/
  | missing
  /-- present, but not of the expected type -/
  | wrongType (want : Ty)
  /-- an array that must have a member has none -/
  | empty
  /-- a string outside the set the convention allows here (the offending text is kept) -/
  | unsupported (got : String)
  /-- a number **written with a minus sign** where the convention allows no negative amount. The test is the sign flag of the lexeme, not the value: a `-0` carries it too, and a reported amount is
  read as the lexeme the provider wrote, never as a float, so this kind means "written negative", not "below zero" -/
  | negative
  deriving DecidableEq, Repr

/-- A refusal: `path` is outermost-first (`choices`, `0`, `message`, ...). -/
structure Fault where
  path : List Step
  kind : Kind
  deriving DecidableEq, Repr

/-- The same refusal one level further in: the failing value sits under `s`. -/
def Fault.under (s : Step) (f : Fault) : Fault := { f with path := s :: f.path }

/-- A fault at the value itself. -/
def Fault.here (k : Kind) : Fault := { path := [], kind := k }

/-- `e` with its fault placed under `s`: the decoder of a member calls this on its error. -/
@[inline] def underStep {α : Type} (s : Step) : Except Fault α → Except Fault α
  | .ok a => .ok a
  | .error f => .error (f.under s)

def Ty.render : Ty → String
  | .object => "an object"
  | .array => "an array"
  | .string => "a string"
  | .natural => "a natural number"
  | .boolean => "a boolean"
  | .number => "a number"

/-- The human-readable text of a kind. `.negative` reads "is written with a minus sign": the rule is about the lexeme's sign, and a `-0` is refused without being below zero. -/
def Kind.render : Kind → String
  | .missing => "is missing"
  | .wrongType t => s!"is not {t.render}"
  | .empty => "is empty"
  | .unsupported g => s!"has an unsupported value {g.quote}"
  | .negative => "is written with a minus sign"

def Step.render : Step → String
  | .key k => "." ++ k
  | .idx i => s!"[{i}]"

/-- A human-readable line: `reply.choices[0].message.content is not a string`. -/
def Fault.render (f : Fault) : String :=
  "reply" ++ String.join (f.path.map Step.render) ++ " " ++ f.kind.render

end VbmLlm
