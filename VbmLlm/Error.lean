/-! # The error taxonomy: the status of a failed call as a closed class

A failed call has an HTTP status; a consumer needs one decision from it, so the status maps **totally** onto a closed set of classes. The map is the wire contract of the conventions (401 and 403 mean the credentials,
402 the quota, 408 a timeout, 429 the rate limit, a server error an overloaded provider), the same for every adapter. What is **not** here: which class to retry, how long to wait, and the words that say a context
was too long (a heuristic of the consumer): `contextWords` is the consumer's verdict on the message, taken as a parameter, and the only way to get `overflow` (a client error whose words say so, never a server's). -/
namespace VbmLlm

inductive ErrorClass where
  /-- 401 or 403: the credentials -/
  | auth
  /-- 402: the quota or the balance -/
  | quota
  /-- 408 -/
  | timeout
  /-- 429 -/
  | rateLimit
  /-- a server error (500 and above, but not the two TLS statuses) -/
  | overloaded
  /-- a client error whose message the consumer reads as a context that is too long -/
  | overflow
  /-- any other client error: the request is not acceptable as sent -/
  | invalid
  deriving DecidableEq, Repr

namespace ErrorClass

def name : ErrorClass → String
  | .auth => "auth"
  | .quota => "quota"
  | .timeout => "timeout"
  | .rateLimit => "rateLimit"
  | .overloaded => "overloaded"
  | .overflow => "overflow"
  | .invalid => "invalid"

/-- The class of the status of a failed call. 525 and 526 (the provider's TLS handshake and certificate) are not an overloaded server: the request cannot succeed as sent. -/
def ofStatus (n : Nat) (contextWords : Bool) : ErrorClass :=
  if n = 401 ∨ n = 403 then .auth
  else if n = 402 then .quota
  else if n = 408 then .timeout
  else if n = 429 then .rateLimit
  else if n = 525 ∨ n = 526 then .invalid
  else if 500 ≤ n then .overloaded
  else if contextWords then .overflow
  else .invalid

end ErrorClass
end VbmLlm
