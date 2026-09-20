import ResourcePrefix
set_option autoImplicit false
namespace ResourcePrefix
namespace Dependent

/- Semantic type constructors over the SAME concrete machine.
   This is not a standalone syntactic dependent type checker. -/
abbrev Before (t s : Task) : Prop := ∃ e, Step s e t
abbrev Returns (p : Code) (x : Val) (es : List Event) (y : Val) : Prop :=
  Prefix (.run p x) es (.done y)

def Good (p : Code) (x : Val) (Q : List Event → Val → Prop) : Prop :=
  Acc Before (.run p x) ∧
  (∀ es t, Prefix (.run p x) es t →
    (∃ v, t = .done v) ∨ ∃ e u, Step t e u) ∧
  (∀ es y, Returns p x es y → Q es y)

/-- Good requires all-path termination, no stuck reachable state, and ALL returns. -/
theorem done_acc (v : Val) : Acc Before (.done v) := by
  apply Acc.intro
  intro t ht
  obtain ⟨e, h⟩ := ht
  cases h

theorem done_prefix {v : Val} {es : List Event} {t : Task}
    (h : Prefix (.done v) es t) : es = [] ∧ t = .done v := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons hs _ => cases hs

/-- A fully characterized one-step primitive satisfies a total contract. -/
theorem primitive_good {p : Code} {x y : Val} {event : Event}
    (shape : ∀ e t, Step (.run p x) e t ↔ e = event ∧ t = .done y)
    {Q : List Event → Val → Prop} (post : Q [event] y) : Good p x Q := by
  refine ⟨?_, ?_, ?_⟩
  · apply Acc.intro
    intro t ht
    obtain ⟨e, hs⟩ := ht
    obtain ⟨_, rfl⟩ := (shape e t).1 hs
    exact done_acc y
  · intro es t hp
    cases hp with
    | nil => exact Or.inr ⟨event, .done y, (shape event (.done y)).2 ⟨rfl,rfl⟩⟩
    | cons hs tail =>
      obtain ⟨_, rfl⟩ := (shape _ _).1 hs
      exact Or.inl ⟨y, (done_prefix tail).2⟩
  · intro es z hp
    cases hp with
    | cons hs tail =>
      obtain ⟨rfl, rfl⟩ := (shape _ _).1 hs
      obtain ⟨rfl, hz⟩ := done_prefix tail
      cases hz
      exact post

structure View where
  Logical : Type
  Holds : Logical → Val → Prop

def Apart (x y : Val) : Prop := ∀ k, x.mass k = 0 ∨ y.mass k = 0

def tensor (A : View) (B : A.Logical → View) : View :=
  ⟨(a : A.Logical) × (B a).Logical,
   fun ab v => ∃ x y, v = .pair x y ∧ A.Holds ab.1 x ∧
     (B ab.1).Holds ab.2 y ∧ Apart x y⟩

/-- Both descriptions concern exactly the SAME physical value. -/
def overlay (A : View) (B : A.Logical → View) : View :=
  ⟨(a : A.Logical) × (B a).Logical,
    fun ab v => A.Holds ab.1 v ∧ (B ab.1).Holds ab.2 v⟩

def refine (A : View) (P : A.Logical → Prop) : View :=
  ⟨{a : A.Logical // P a}, fun a v => A.Holds a.val v⟩

def erasedAll (I : Type) (B : I → View) : View :=
  ⟨(i : I) → (B i).Logical, fun f v => ∀ i, (B i).Holds (f i) v⟩

def erasedExists (I : Type) (B : I → View) : View :=
  ⟨(i : I) × (B i).Logical, fun ib v => (B ib.1).Holds ib.2 v⟩

/-- Private environments are NOT exposed in the public dependent function type. -/
def pi (A : View) (B : A.Logical → View) : View :=
  ⟨(a : A.Logical) → (B a).Logical,
    fun f v => ∃ body env, v = .closure body env ∧
      ∀ a x, A.Holds a x → Apart env x →
        Good body (.pair env x) (fun _ y => (B a).Holds (f a) y)⟩

def Implements (p : Code) (A : View) (B : A.Logical → View)
    (f : (a : A.Logical) → (B a).Logical) : Prop :=
  ∀ a x, A.Holds a x → Good p x (fun _ y => (B a).Holds (f a) y)

/-- A dependent output can refer to BOTH the logical capture and the argument. -/
theorem dependent_curry {E A : View}
    {B : E.Logical → A.Logical → View} {p : Code}
    {f : (e : E.Logical) → (a : A.Logical) → (B e a).Logical}
    (body : Implements p (tensor E (fun _ => A))
      (fun ea => B ea.1 ea.2) (fun ea => f ea.1 ea.2)) :
    Implements (.curry p) E (fun e => pi A (B e)) f := by
  intro e env he
  apply primitive_good (event := .quiet) (y := .closure p env)
  · intro event t
    constructor
    · intro hs; cases hs; exact ⟨rfl,rfl⟩
    · rintro ⟨rfl,rfl⟩; exact .curry p env
  · refine ⟨p, env, rfl, ?_⟩
    intro a x ha hsep
    exact body ⟨e,a⟩ (.pair env x) ⟨env,x,rfl,he,ha,hsep⟩

/-- Applying a represented dependent function is total on disjoint represented inputs. -/
theorem dependent_apply {A : View} {B : A.Logical → View}
    {f : (a : A.Logical) → (B a).Logical} {vf : Val}
    (hf : (pi A B).Holds f vf)
    {a : A.Logical} {x : Val} (hx : A.Holds a x) (ha : Apart vf x) :
    Good .app (.pair vf x) (fun _ y => (B a).Holds (f a) y) := by
  obtain ⟨p,env,rfl,h⟩ := hf
  have hb := h a x hx (by simpa [Apart, Val.mass] using ha)
  refine ⟨?_, ?_, ?_⟩
  · apply Acc.intro
    intro t ht
    obtain ⟨event, hs⟩ := ht
    cases hs
    exact hb.1
  · intro es t hp
    cases hp with
    | nil => exact Or.inr ⟨.quiet, .run p (.pair env x), .app p env x⟩
    | cons hs tail =>
      cases hs
      exact hb.2.1 _ _ tail
  · intro es y hp
    cases hp with
    | cons hs tail =>
      cases hs
      exact hb.2.2 _ _ tail

/-- The same q works for all erased witnesses; no per-witness code choice. -/
theorem eliminate_erased {I : Type} {B : I → View} {C : View}
    {q : Code} {f : (i : I) → (B i).Logical → C.Logical}
    (h : ∀ i, Implements q (B i) (fun _ => C) (f i)) :
    Implements q (erasedExists I B) (fun _ => C) (fun ib => f ib.1 ib.2) := by
  intro ib x hx
  exact h ib.1 ib.2 x hx

/-- Combining proofs constrains the same execution, not two favorable runs. -/
theorem same_run_intersection {p : Code} {x : Val}
    {P Q : List Event → Val → Prop} (hp : Good p x P) (hq : Good p x Q) :
    Good p x (fun es y => P es y ∧ Q es y) := by
  exact ⟨hp.1, hp.2.1, fun es y h => ⟨hp.2.2 es y h, hq.2.2 es y h⟩⟩

/-- Resource preservation is inherited from the machine, not a type-level assumption. -/
theorem typed_prefix_unique {p : Code} {x : Val} {A : View}
    {B : A.Logical → View} {f : (a : A.Logical) → (B a).Logical}
    (_hp : Implements p A B f) (hx : Unique (.run p x))
    {es : List Event} {t : Task} (h : Prefix (.run p x) es t) : Unique t :=
  unique_at_every_prefix hx h

def natView : View := ⟨Nat, fun n v => v = .nat n⟩
def tokenView (k : Nat) : View := ⟨Unit, fun _ v => v = .token k⟩

theorem identity_refine (A : View) :
    Implements .skip A (fun a => refine A (fun b => b = a)) (fun a => ⟨a,rfl⟩) := by
  intro a x hx
  apply primitive_good (event := .quiet) (y := x)
  · intro event t
    constructor
    · intro hs; cases hs; exact ⟨rfl,rfl⟩
    · rintro ⟨rfl,rfl⟩; exact .skip x
  · exact hx

/-- The result type specifies both the captured owner and the actual numeric argument. -/
def ownedResult (k n : Nat) : View :=
  refine (tensor (tokenView k) (fun _ => natView)) (fun pair => pair = ⟨(),n⟩)

theorem owned_closure_total (k : Nat) :
    (pi natView (ownedResult k)).Holds (fun n => ⟨⟨(),n⟩,rfl⟩)
      (.closure .skip (.token k)) := by
  refine ⟨.skip, .token k, rfl, ?_⟩
  intro n x hx ha
  apply primitive_good (event := .quiet) (y := .pair (.token k) x)
  · intro event t
    constructor
    · intro hs; cases hs; exact ⟨rfl,rfl⟩
    · rintro ⟨rfl,rfl⟩; exact .skip _
  · exact ⟨.token k,x,rfl,rfl,hx,ha⟩

#print axioms primitive_good
#print axioms dependent_curry
#print axioms dependent_apply
#print axioms eliminate_erased
#print axioms same_run_intersection
#print axioms typed_prefix_unique
#print axioms identity_refine
#print axioms owned_closure_total
end Dependent
end ResourcePrefix
