-- import the definitions of uniform space via covers
import uniform_structure.covers

-- import the definition of pseudometric space
import pseudometric_space

-- In this exercise we will show that a pseudometric on a set X 
-- gives rise to a distinguished family of covers for X 
-- which make X into a "uniform space in the sense of covers"

-- This is a question about pseudometrics so let's put it
-- in the pseudometric namespace

namespace pseudometric

-- Let X be a set (or a type), and let d be a pseudometric on X
variables {X : Type} (d : X → X → ℝ) [is_pseudometric d]

-- let's define a closed ball

/-- Closed ball centre x radius ε -/
def closed_ball (x : X) (ε : ℝ) := {y : X | d x y ≤ ε}

-- definition of closed ball
lemma mem_closed_ball {x y : X} {ε : ℝ} : y ∈ closed_ball d x ε ↔ d x y ≤ ε :=
iff.rfl -- true by definition

-- Here's an obvious lemma: if 0 ≤ ε then x is in the closed ball centre x
-- and radius ε

lemma self_mem_ball (x : X) (ε : ℝ) (hε : 0 ≤ ε) : x ∈ closed_ball d x ε :=
begin
  rw mem_closed_ball,
  rw d_self d,
  assumption
end

-- Define Θ to be the set of covers of X with the following property:
-- there exists ε ≥ 0 such that each set in the cover contains a closed ball
-- of radius ε (note that ε is independent of which set in the cover)

def Θ : set (cover X) :=
  {𝒞 | ∃ ε (hε : 0 ≤ ε), ∀ U ∈ 𝒞.C, ∃ x : X, closed_ball d x ε ⊆ U}

-- a cover is in Θ iff it's a closed ball cover, or the universal cover
-- the proof is obvious
lemma mem_Θ (𝒞 : cover X) : 𝒞 ∈ Θ d ↔
  ∃ ε (hε : 0 ≤ ε), ∀ U ∈ 𝒞.C, ∃ x : X, closed_ball d x ε ⊆ U := iff.rfl -- true by definition

-- The exerise is to show that the 3 axioms for a distinguished family are
-- satisfied by Θ

-- Axiom 1: the universal cover is in
lemma univ_mem : univ_cover X ∈ Θ d :=
begin
  sorry
end

-- Axiom 2 : anything star-bigger than a distinguished cover is distinguished
lemma star_mem (P Q : cover X) (hP : P ∈ Θ d) (hPQ : P <* Q) : Q ∈ Θ d :=
begin
  sorry
end

lemma ub_mem (P Q : cover X) (hP : P ∈ Θ d) (hQ : Q ∈ Θ d) :
  ∃ R : cover X, R ∈ Θ d ∧ P <* R ∧ Q <* R :=
begin
  sorry
end
 
definition to_cover : dist_covers X :=
{ Θ := Θ d,
  univ_mem := univ_mem d,
  star_mem := star_mem d,
  ub_mem := ub_mem d}

end pseudometric