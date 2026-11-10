module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-! The seven-eighths Hecke nonvanishing theorem from certified moment estimates. -/

namespace SevenEighths.HeckeFamily

theorem LFunction_ne_zero_of_certified_bands
    (h : ProbeFinalAssemblyCertifiedBands.DetectorCertifiedBands)
    (χ : Character) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) : LFunction χ s ≠ 0 := by
  apply ProbeFinalAssembly.hecke_of_chosen_moments
    (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified h) χ s hs
  by_cases hs1 : s = 1
  · exact Or.inr (fun hχ => hpole ⟨hχ, hs1⟩)
  · exact Or.inl hs1

end SevenEighths.HeckeFamily

end OAI
