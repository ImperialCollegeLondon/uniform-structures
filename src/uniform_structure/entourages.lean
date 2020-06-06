import tactic

/-!

# The entourage definition of a uniform space

We start with a little section on `U ∘ V` (see axiom 4 of the wikipedia
entourage definition of a uniform space)

We then give the entourage definition of a uniform space

-/

-- We first define U ∘ V. First the function itself (called `comp_ent`)

/-- composition `∘` of two subsets of X × X -/
def comp_ent {X : Type} (U V : set (X×X)) :=
  {p : X × X | ∃z : X, (p.1, z) ∈ U ∧ (z, p.2) ∈ V}

-- and now the notation
notation U ` ∘ ` V := comp_ent U V

variables {X : Type} {U V : set (X × X)} {x y : X}

/-- This is the theorem which gives the defining property of U ∘ V -/
@[simp] theorem mem_comp_ent :
  (x, y) ∈ U ∘ V ↔ ∃ z, (x, z) ∈ U ∧ (z, y) ∈ V := iff.rfl -- true by definition

structure uniform_space_entourage (X : Type) :=
(entourages : set (set (X × X)))
-- now go through the five axioms in Wikipedia
(refl : ∀ U ∈ entourages, ∀ x : X, (x,x) ∈ U)
(bigger : ∀ U V : set (X × X), U ∈ entourages → U ⊆ V → V ∈ entourages)
(inter : ∀ U V ∈ entourages, U ∩ V ∈ entourages)
(comp : ∀ U ∈ entourages, ∃ V ∈ entourages, V ∘ V ⊆ U)
(symm : ∀ U ∈ entourages, {z : X × X | (z.2, z.1) ∈ U} ∈ entourages)

