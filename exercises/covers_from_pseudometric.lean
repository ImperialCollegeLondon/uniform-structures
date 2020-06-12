-- import the definitions of uniform space via covers
import uniform_structure.covers

-- import the definition of pseudometric space
import pseudometric_space

-- In this exercise we will show that a pseudometric on a set X 
-- gives rise to a distinguished family of covers for X 
-- which make X into a "uniform space in the sense of covers"

-- This is a question about pseudometrics so let's put it
-- in the pseudometric namespace

open set

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

-- It's useful to know that the collection of closed balls radius ε
-- is a cover. 

def closed_ball_cover (ε : ℝ) (hε : 0 ≤ ε) : cover X :=
{ C := {C : set X | ∃ x : X, C = closed_ball d x ε},
  cov := begin
    intro x,
    use closed_ball d x ε,
    split,
    { use x},
    { apply self_mem_ball d x ε hε,}
  end
}

-- Define Θ to be the set of covers of X with the following property:
-- there exists ε ≥ 0 such that each set in the cover contains a closed ball
-- of radius ε (note that ε is independent of which set in the cover)

def Θ : set (cover X) :=
  {𝒞 | ∃ ε (hε : 0 < ε), ∀ x : X, ∃ U ∈ 𝒞.C, closed_ball d x ε ⊆ U}

-- a cover is in Θ iff it's a closed ball cover, or the universal cover
-- the proof is obvious
lemma mem_Θ (𝒞 : cover X) : 𝒞 ∈ Θ d ↔
  ∃ ε (hε : 0 < ε), ∀ x : X, ∃ U ∈ 𝒞.C, closed_ball d x ε ⊆ U := iff.rfl -- true by definition

-- The exerise is to show that the 3 axioms for a distinguished family are
-- satisfied by Θ

-- Axiom 1: the universal cover is in
lemma univ_mem : univ_cover X ∈ Θ d :=
begin
  rw mem_Θ,
  use 1,
  split, linarith,
  intro x,
  use univ,
  simp [univ_cover],
end

-- Axiom 2 : anything star-bigger than a distinguished cover is distinguished
lemma star_mem (P Q : cover X) (hP : P ∈ Θ d) (hPQ : P <* Q) : Q ∈ Θ d :=
begin
  rw mem_Θ at hP ⊢,
  rcases hP with ⟨ε, hε, hεU⟩,
  use ε,
  split, linarith,
  intro x,
  rcases hεU x with ⟨V, hV, hεV⟩,
  rw star_ref_iff at hPQ,
  specialize hPQ V hV,
  rcases hPQ with ⟨W, hW, hVW⟩,
  use W,
  use hW,
  refine subset.trans hεV (hVW V hV _),
  rw ne_empty_iff_nonempty,
  use x,
  simp,
  apply hεV,
  rw mem_closed_ball,
  rw d_self d x,
  linarith,
end

-- Axiom 3: two covers have an upper bound in the <* ordering
lemma ub_mem (P Q : cover X) (hP : P ∈ Θ d) (hQ : Q ∈ Θ d) :
  ∃ R : cover X, R ∈ Θ d ∧ R <* P ∧ R <* Q :=
begin
  rw mem_Θ at hP hQ,
  rcases hP with ⟨εP, hεP, hP⟩,
  rcases hQ with ⟨εQ, hεQ, hQ⟩,
  have hε : 0 < min εP εQ,
    apply lt_min; linarith,
  set ε := min εP εQ / 3 with hε,
  use closed_ball_cover d ε (by linarith),
  split,
  { rw mem_Θ,
    use ε,
    split, linarith,
    intro x,
    use closed_ball d x ε,
    split, swap, refl,
    simp [closed_ball_cover],
    use x,
  },
  split,
  { rw star_ref_iff,
    rintros _ ⟨x, rfl⟩,
    rcases hP x with ⟨U, hUP, hUε⟩, -- <- changes to rcases hQ x
    use [U, hUP],
    rintros _ ⟨y, rfl⟩ hxy,
    rw ne_empty_iff_nonempty at hxy,
    rcases hxy with ⟨z, hzx, hzy⟩,
    refine subset.trans _ hUε,
    intros t hty,
    rw mem_closed_ball at ⊢ hzx hzy hty,
    suffices : d x t ≤ 3 * ε,
    { refine le_trans this _,
      rw hε,
      convert min_le_left εP εQ, -- <- changes to min_le_right
      linarith,
    },
    calc d x t ≤ d x z + d z t : d_triangle d x z t
    ...        ≤ d x z + (d z y + d y t) : by linarith [d_triangle d z y t]
    ...        = d x z + (d y z + d y t) : by rw d_comm d z y
    ...        ≤ 3 * ε : by linarith
  },
  { rw star_ref_iff,
    rintros _ ⟨x, rfl⟩,
    rcases hQ x with ⟨U, hUQ, hUε⟩,
    use [U, hUQ],
    rintros _ ⟨y, rfl⟩ hxy,
    rw ne_empty_iff_nonempty at hxy,
    rcases hxy with ⟨z, hzx, hzy⟩,
    refine subset.trans _ hUε,
    intros t hty,
    rw mem_closed_ball at ⊢ hzx hzy hty,
    suffices : d x t ≤ 3 * ε,
    { refine le_trans this _,
      rw hε,
      convert min_le_right εP εQ,
      linarith,
    },
    calc d x t ≤ d x z + d z t : d_triangle d x z t
    ...        ≤ d x z + (d z y + d y t) : by linarith [d_triangle d z y t]
    ...        = d x z + (d y z + d y t) : by rw d_comm d z y
    ...        ≤ 3 * ε : by linarith
  },
end
 
definition to_cover : dist_covers X :=
{ Θ := Θ d,
  univ_mem := univ_mem d,
  star_mem := star_mem d,
  ub_mem := ub_mem d}

end pseudometric