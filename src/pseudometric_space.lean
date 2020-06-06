import topology.metric_space.basic

/-!

# Pseudometric spaces

A pseudometric on a set (or type) X is a distance function obeying
all the axioms of a metric except possible d(x,y)=0 ↔ x = y.

-/

/-- A function d : X^2 → ℝ is a *pseudometric* if it satisfies the axioms
  for a metric space apart from possibly the axiom saying d(x,y)=0 -> x=y -/ 
class is_pseudometric {X : Type} (d : X → X → ℝ) :=
(d_self : ∀ x : X, d x x = 0)
(d_comm : ∀ x y : X, d x y = d y x)
(d_triangle : ∀ x y z : X, d x z ≤ d x y + d y z)

-- ignore this boilerplate code: it's restating the lemmas to make them easier to use

variable {X : Type}

lemma d_self (d : X → X → ℝ) [is_pseudometric d] :
  ∀ x : X, d x x = 0 := @is_pseudometric.d_self X d _

lemma d_comm (d : X → X → ℝ) [is_pseudometric d] :
  ∀ x y : X, d x y = d y x := @is_pseudometric.d_comm X d _

lemma d_triangle (d : X → X → ℝ) [is_pseudometric d] :
  ∀ x y z : X, d x z ≤ d x y + d y z := @is_pseudometric.d_triangle X d _

-- fun fact: we never included the axiom that d x y ≥ 0, because it follows
-- from the other axioms!

variables (d : X → X → ℝ) [is_pseudometric d]

theorem d_nonneg {x y : X} : 0 ≤ d x y :=
begin

  -- First note 0 = d(x,x) ≤ d(x,y)+d(y,x) = 2d(x,y)

  have h2 : 0 ≤ 2 * d x y,
    calc 0 = d x x : by rw d_self d
    ...    ≤ d x y + d y x : by refine d_triangle d _ _ _
    ...    = d x y + d x y : by rw d_comm d
    ...    = 2 * d x y : by ring,

  -- and now the result is obvious

  linarith
end

