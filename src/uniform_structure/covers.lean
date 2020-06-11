import tactic
import data.set.basic

open set

/-- a cover of X is a set of subsets of X whose union is X -/
structure cover (X : Type) :=
(C : set (set X))
(cov : ∀ x : X, ∃ U ∈ C, x ∈ U)

-- note that the subset X of X isn't called X! X is a type. The subset X of X
-- is called `univ`

/-- The cover {X} of X -/
def univ_cover (X : Type) : cover X :=
{ C := {univ},
  cov := by simp} -- proof it's a cover is obvious and `simp` finds it

variable {X : Type}

-- definition of star refinement
def star_ref (P : cover X) (Q : cover X) :=
∀ A ∈ P.C, ∃ U ∈ Q.C, ∀ B ∈ P.C, A ∩ B ≠ ∅ → B ⊆ U

-- this may or may not work, Lean might get confused because `<` means something else
notation P `<*` Q := star_ref P Q

/-
    {X} is a uniform cover (i.e. {X} ∈ Θ).
    If P <* Q and P is a uniform cover, then Q is also a uniform cover.
    If P and Q are uniform covers, then there is a uniform cover R that 
    star-refines both P and Q.

Given a point x and a uniform cover P, one can consider the union of the members of P that contain x as a typical neighbourhood of x of "size" P, and this intuitive measure applies uniformly over the space.

Given a uniform space in the entourage sense, define a cover P to be uniform if there is some entourage U such that for each x ∈ X, there is an A ∈ P such that U[x] ⊆ A. These uniform covers form a uniform space as in the second definition. Conversely, given a uniform space in the uniform cover sense, the supersets of ⋃{A × A : A ∈ P}, as P ranges over the uniform covers, are the entourages for a uniform space as in the first definition. Moreover, these two transformations are inverses of each other. 
-/

/-- A distinguished family of covers for a set X is a filter for <*  -/
structure dist_covers (X : Type) :=
-- collection of covers
(Θ : set (cover X) )
-- {X} is in Θ
(univ_mem : univ_cover X ∈ Θ)
-- if P is in Θ and P <* Q then Q is in Θ
(star_mem (P Q : cover X) (hP : P ∈ Θ) (hPQ : P <* Q) : Q ∈ Θ)
-- if P, Q ∈ Θ then there exists R ∈ Θ with P <* R and Q <* R
(ub_mem (P Q : cover X) (hP : P ∈ Θ) (hQ : Q ∈ Θ) : ∃ R : cover X, R ∈ Θ ∧ P <* R ∧ Q <* R)
