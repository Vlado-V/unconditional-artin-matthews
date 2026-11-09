module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The original admissible modulus family and an explicit plateau subset. -/

noncomputable section
namespace ArtinMatthews

def circleModuli (F r L : ℕ) : Finset ℕ :=
  (Finset.Icc (3 * L) (6 * L)).filter (fun q => F ∣ q ∧ q.Coprime r)

def circleBlockLength (F r L : ℕ) : ℕ := L / (2 * (F * r))

def circleResidueBlocks (F r L : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (circleBlockLength F r L)).product
    ((Finset.range r).filter (fun a => r.Coprime a))

def circleBlockModulus (F r L : ℕ) (p : ℕ × ℕ) : ℕ :=
  F * (r * (4 * L / (F * r) + 1 + p.1) + p.2)

def circlePlateauModuli (F r L : ℕ) : Finset ℕ :=
  (circleResidueBlocks F r L).image (circleBlockModulus F r L)

end ArtinMatthews
