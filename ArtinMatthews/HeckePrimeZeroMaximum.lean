module

public import OAI.NumberTheory.DirichletL.Hecke.DetectorZeros
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.Hecke.Nonvanishing


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Hecke zero maximum is bounded by the proved seven-eighths
nonvanishing theorem. No zero-location hypothesis is retained. -/

namespace ArtinMatthews
open OAI.SevenEighths

theorem heckeZeroMaximum_le_seven_eighths {ι : Type*} [Fintype ι]
    (η : ι → HeckeFamily.Character) (hη : ∀ i, (η i).residue ≠ 1) (T : ℝ) :
    HeckeDetectorZeros.zeroMaximum η hη T ≤ 7/8 := by
  by_contra h
  have hmax : 51/100 < HeckeDetectorZeros.zeroMaximum η hη T := by linarith
  obtain ⟨i, s, hzero, _, hre⟩ := HeckeDetectorZeros.maximum_attained η hη T hmax
  exact HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re (η i)
    (by rw [hre]; exact lt_of_not_ge h) (fun hpole => hη i hpole.1) hzero

end ArtinMatthews
