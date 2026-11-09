module

public import ArtinMatthews.SpectralABLSameCuspAtkinLehner
public import ArtinMatthews.SpectralBareModulusSeries


set_option backward.privateInPublic true
@[expose] public section

/-! The actual diagonal bare series is indexed by the positive multiples
of the level, with its literal Bessel argument and Fourier normalization. -/

noncomputable section
open Set
open scoped MatrixGroups
open OAI.Erdos970.ErdosKloosterman

namespace ArtinMatthews

def spectralABLDiagonalBareAmplitude (H : ℂ → ℂ) (n : ℤ) (X : ℝ) : ℂ :=
  ((X/2 : ℝ) : ℂ)*spectralABLBareKernel H n n X

def gamma0AtkinSameCuspBareSummand (N : ℕ) [NeZero N] (n : ℤ) (H : ℂ → ℂ) (k : ℕ) : ℂ :=
  standardSum (N*(k+1)) n n/((N*(k+1) : ℕ) : ℂ)*
    spectralABLDiagonalBareAmplitude H n (2*|cuspFourierFrequency 1 n|/((N*(k+1) : ℕ) : ℝ))

theorem gamma0AtkinSameCusp_bareFibre_zero (r s : ℕ) [NeZero r] [NeZero s]
    (c : Ioi (0 : ℕ)) (hc : ¬ s ∣ c.val) (n : ℤ) (H : ℂ → ℂ) :
    gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) c n n H = 0 := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  simp only [gamma0TrueWidthBareFibre,
    gamma0MixedSameCuspKloosterman_zero_of_not_dvd r s c.val hc n n, zero_mul]

theorem gamma0AtkinSameCusp_bareFibre_index (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (k : ℕ) (n : ℤ) (H : ℂ → ℂ) :
    gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s)
      (gamma0AtkinSameCuspIndex s k) n n H =
        gamma0AtkinSameCuspBareSummand (r*s) n H k := by
  let d := k+1
  let C := (r*s)*d
  let q := |cuspFourierFrequency 1 n|
  let _ : NeZero d := ⟨Nat.succ_ne_zero k⟩
  have hC : 0 < (C : ℝ) := Nat.cast_pos.mpr (NeZero.pos C)
  have hmod : gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s)
      (s*d : ℕ) = (C : ℝ) := by
    rw [gamma0AtkinSameCusp_modulus r s (s*d) hcop, ← Nat.mul_assoc]
  have hKS : gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s)
      (gamma0CuspOneOver s) (s*d) n n = standardSum C n n := by
    simpa only [← Nat.mul_assoc, C] using gamma0MixedSameCuspKloosterman_diag_eq_standard r s d hcop n
  have hq : Real.sqrt (q*q) = q := by rw [← sq, Real.sqrt_sq (abs_nonneg _)]
  unfold gamma0TrueWidthBareFibre
  dsimp only
  change gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s)
    (s*d) n n * ((Real.sqrt (q*q) /
      (gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*d : ℕ))^2 : ℝ) : ℂ) *
    spectralABLBareKernel H n n (Real.sqrt (q*q) *
      (2/gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*d : ℕ))) = _
  rw [hKS, hmod, hq, show q*(2/(C : ℝ)) = 2*q/(C : ℝ) by ring]
  change standardSum C n n * ((q/(C : ℝ)^2 : ℝ) : ℂ) *
    spectralABLBareKernel H n n (2*q/(C : ℝ)) =
    standardSum C n n/(C : ℂ)*((((2*q/(C : ℝ))/2 : ℝ) : ℂ) *
      spectralABLBareKernel H n n (2*q/(C : ℝ)))
  have hscalar : (((2*q/(C : ℝ))/2 : ℝ) : ℂ) = (q : ℂ)/(C : ℂ) := by
    push_cast
    ring
  rw [hscalar]
  push_cast
  ring

theorem gamma0AtkinSameCusp_bareSeries_reindex (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (n : ℤ) (H : ℂ → ℂ) :
    let f (c : Ioi (0 : ℕ)) := gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s)
      (gamma0CuspOneOver s) c n n H
    (Summable f ↔ Summable (gamma0AtkinSameCuspBareSummand (r*s) n H)) ∧
      (∑' c, f c) = ∑' k, gamma0AtkinSameCuspBareSummand (r*s) n H k := by
  let f (c : Ioi (0 : ℕ)) := gamma0TrueWidthBareFibre (r*s) (gamma0CuspOneOver s)
    (gamma0CuspOneOver s) c n n H
  let e := gamma0AtkinSameCuspIndex s
  change (Summable f ↔ Summable _) ∧ (∑' c, f c) = _
  have hzero (c : Ioi (0 : ℕ)) (hc : c ∉ range e) : f c = 0 :=
    gamma0AtkinSameCusp_bareFibre_zero r s c
      (fun h => hc ((gamma0AtkinSameCuspIndex_range s c).mpr h)) n H
  have heq : f ∘ e = gamma0AtkinSameCuspBareSummand (r*s) n H :=
    funext (fun k => gamma0AtkinSameCusp_bareFibre_index r s hcop k n H)
  have hs := e.injective.summable_iff (f := f) hzero
  rw [heq] at hs
  refine ⟨hs.symm, ?_⟩
  have hsup : Function.support f ⊆ range e := by
    intro c hc
    by_contra h
    exact hc (hzero c h)
  calc
    _ = ∑' k, (f ∘ e) k := (e.injective.tsum_eq hsup).symm
    _ = _ := by rw [heq]

end ArtinMatthews
