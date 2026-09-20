import Lean
set_option autoImplicit false
namespace ResourcePrefix

/- A standalone research kernel, not a complete dependent type theory.
   Resource safety is checked for all finite prefixes, not only returned values.
   No allocation, shared heap, target compiler or full type checker is modeled. -/
inductive Code where
  | skip
  | seq (p q : Code)
  | par (p q : Code)
  | curry (p : Code)
  | app
  | literal (n : Nat)
  | add
  | copyNat
  | release
  | emit (n : Nat)
  | repeat (p : Code)

inductive Val where
  | unit
  | nat (n : Nat)
  | token (k : Nat)
  | pair (x y : Val)
  | closure (p : Code) (env : Val)

def Val.mass (k : Nat) : Val → Nat
  | .unit => 0
  | .nat _ => 0
  | .token j => if k = j then 1 else 0
  | .pair x y => x.mass k + y.mass k
  | .closure _ env => env.mass k

inductive Task where
  | done (v : Val)
  | run (p : Code) (v : Val)
  | next (s : Task) (q : Code)
  | both (s t : Task)

def Task.mass (k : Nat) : Task → Nat
  | .done v => v.mass k
  | .run _ v => v.mass k
  | .next s _ => s.mass k
  | .both s t => s.mass k + t.mass k

inductive Event where
  | quiet
  | release (k : Nat)
  | output (n : Nat)

def Event.spent (k : Nat) : Event → Nat
  | .release j => if k = j then 1 else 0
  | _ => 0

inductive Step : Task → Event → Task → Prop where
  | skip (v : Val) :
      Step (.run .skip v) .quiet (.done v)
  | seq (p q : Code) (v : Val) :
      Step (.run (.seq p q) v) .quiet (.next (.run p v) q)
  | nextStep {s s' : Task} {e : Event} {q : Code} :
      Step s e s' → Step (.next s q) e (.next s' q)
  | nextDone (v : Val) (q : Code) :
      Step (.next (.done v) q) .quiet (.run q v)
  | par (p q : Code) (x y : Val) :
      Step (.run (.par p q) (.pair x y)) .quiet
        (.both (.run p x) (.run q y))
  | left {s s' t : Task} {e : Event} :
      Step s e s' → Step (.both s t) e (.both s' t)
  | right {s t t' : Task} {e : Event} :
      Step t e t' → Step (.both s t) e (.both s t')
  | joined (x y : Val) :
      Step (.both (.done x) (.done y)) .quiet (.done (.pair x y))
  | curry (p : Code) (env : Val) :
      Step (.run (.curry p) env) .quiet (.done (.closure p env))
  | app (p : Code) (env arg : Val) :
      Step (.run .app (.pair (.closure p env) arg)) .quiet
        (.run p (.pair env arg))
  | literal (n : Nat) :
      Step (.run (.literal n) .unit) .quiet (.done (.nat n))
  | add (m n : Nat) :
      Step (.run .add (.pair (.nat m) (.nat n))) .quiet (.done (.nat (m+n)))
  | copyNat (n : Nat) :
      Step (.run .copyNat (.nat n)) .quiet (.done (.pair (.nat n) (.nat n)))
  | release (k : Nat) :
      Step (.run .release (.token k)) (.release k) (.done .unit)
  | emit (n : Nat) (v : Val) :
      Step (.run (.emit n) v) (.output n) (.done v)
  | repeat (p : Code) (v : Val) :
      Step (.run (.repeat p) v) .quiet (.next (.run p v) (.repeat p))

/-- Derived from concrete execution rules; balance is not a premise. -/
theorem step_balance {s t : Task} {e : Event}
    (h : Step s e t) (k : Nat) :
    s.mass k = t.mass k + e.spent k := by
  induction h <;> simp_all [Task.mass, Val.mass, Event.spent] <;> omega

inductive Prefix : Task → List Event → Task → Prop where
  | nil (s : Task) : Prefix s [] s
  | cons {s t u : Task} {e : Event} {es : List Event} :
      Step s e t → Prefix t es u → Prefix s (e :: es) u

def spent (k : Nat) : List Event → Nat
  | [] => 0
  | e :: es => e.spent k + spent k es

/-- All finite prefixes, including arbitrary interleavings and loops. -/
theorem prefix_balance {s t : Task} {es : List Event}
    (h : Prefix s es t) (k : Nat) :
    s.mass k = t.mass k + spent k es := by
  induction h with
  | nil => simp [spent]
  | cons hs _ ih =>
      have hstep := step_balance hs k
      simp only [spent]
      omega

def Unique (s : Task) : Prop := ∀ k, s.mass k ≤ 1

theorem unique_at_every_prefix {s t : Task} {es : List Event}
    (hs : Unique s) (h : Prefix s es t) : Unique t := by
  intro k
  have hb := prefix_balance h k
  have hu := hs k
  omega

theorem no_double_release {s t : Task} {es : List Event}
    (hs : Unique s) (h : Prefix s es t) (k : Nat) : spent k es ≤ 1 := by
  have hb := prefix_balance h k
  have hu := hs k
  omega

theorem no_token_copy (p : Code) (k : Nat) (es : List Event) :
    ¬ Prefix (.run p (.token k)) es (.done (.pair (.token k) (.token k))) := by
  intro h
  have hb := prefix_balance h k
  simp [Task.mass, Val.mass] at hb
  omega

/-- Uniformity must constrain all outcomes, not merely a lucky execution. -/
theorem no_uniform_bit {Program : Type} (Returns : Program → Nat → Prop) :
    ¬ ∃ p, (∃ n, Returns p n) ∧
      (∀ b : Bool, ∀ n, Returns p n → n = (if b then 1 else 0)) := by
  rintro ⟨p, ⟨n, hn⟩, h⟩
  have h0 := h false n hn
  have h1 := h true n hn
  simp at h0 h1
  omega

#print axioms step_balance
#print axioms prefix_balance
#print axioms unique_at_every_prefix
#print axioms no_double_release
#print axioms no_token_copy
#print axioms no_uniform_bit
end ResourcePrefix
