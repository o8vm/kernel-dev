import ResourcePrefix
set_option autoImplicit false
namespace ResourcePrefix

theorem append_prefix {s t u : Task} {xs ys : List Event}
    (h : Prefix s xs t) (g : Prefix t ys u) : Prefix s (xs ++ ys) u := by
  induction h with
  | nil => exact g
  | cons hstep _ ih => exact .cons hstep (ih g)

/-- A real captured owner is returned by a later higher-order invocation. -/
theorem owned_call (k n label : Nat) :
    Prefix
      (.run .app (.pair (.closure (.emit label) (.token k)) (.nat n)))
      [.quiet, .output label]
      (.done (.pair (.token k) (.nat n))) := by
  exact .cons (.app (.emit label) (.token k) (.nat n))
    (.cons (.emit label (.pair (.token k) (.nat n))) (.nil _))

def forked (k n : Nat) : Task :=
  .run (.par (.emit 1) (.emit 2)) (.pair (.token k) (.nat n))

/-- Both schedules are represented, rather than serializing the two traces. -/
theorem both_orders (k n : Nat) :
    Prefix (forked k n) [.quiet, .output 1, .output 2, .quiet]
      (.done (.pair (.token k) (.nat n))) ∧
    Prefix (forked k n) [.quiet, .output 2, .output 1, .quiet]
      (.done (.pair (.token k) (.nat n))) := by
  constructor
  · exact .cons (.par (.emit 1) (.emit 2) (.token k) (.nat n))
      (.cons (.left (.emit 1 (.token k)))
        (.cons (.right (.emit 2 (.nat n)))
          (.cons (.joined (.token k) (.nat n)) (.nil _))))
  · exact .cons (.par (.emit 1) (.emit 2) (.token k) (.nat n))
      (.cons (.right (.emit 2 (.nat n)))
        (.cons (.left (.emit 1 (.token k)))
          (.cons (.joined (.token k) (.nat n)) (.nil _))))

def spinning (k label : Nat) : Task := .run (.repeat (.emit label)) (.token k)

def pulses (label : Nat) : Nat → List Event
  | 0 => []
  | n+1 => [.quiet, .output label, .quiet] ++ pulses label n

theorem repeat_cycle (k label : Nat) :
    Prefix (spinning k label) [.quiet, .output label, .quiet] (spinning k label) := by
  exact .cons (.repeat (.emit label) (.token k))
    (.cons (.nextStep (.emit label (.token k)))
      (.cons (.nextDone (.token k) (.repeat (.emit label))) (.nil _)))

/-- Arbitrarily long looping prefixes; no fixed fuel or test bound is used. -/
theorem repeat_prefix (k label n : Nat) :
    Prefix (spinning k label) (pulses label n) (spinning k label) := by
  induction n with
  | zero => exact .nil _
  | succ n ih => exact append_prefix (repeat_cycle k label) ih

#print axioms append_prefix
#print axioms owned_call
#print axioms both_orders
#print axioms repeat_prefix
end ResourcePrefix
