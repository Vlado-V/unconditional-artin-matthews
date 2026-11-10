module

public import ArtinMatthews.SpectralPeterssonGram
public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.AtkinLehnerMixedWeight
public import ArtinMatthews.SpectralABLSameCuspAtkinLehner
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralInfinityKloostermanWeil
public import ArtinMatthews.SpectralMixedSameCuspKloosterman
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The literal same-cusp Petersson modulus series at an exact-divisor cusp. -/

noncomputable section
open Matrix Set OAI.Erdos970.ErdosKloosterman
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0PeterssonKloostermanModulusTerm (N : ℕ) [NeZero N] (b a : SL(2, ℤ))
    (m n : ℤ) (W : ℝ → ℂ) (c : Ioi (0 : ℕ)) : ℂ :=
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  gamma0TrueWidthKloostermanSum N b a c.val n m * W (gamma0TrueWidthModulus N b a (c.val : ℝ))

def gamma0PeterssonOrdinaryModulusTerm (N : ℕ) [NeZero N] (m n : ℤ)
    (W : ℝ → ℂ) (j : ℕ) : ℂ :=
  let _ : NeZero (j+1) := ⟨Nat.succ_ne_zero j⟩
  standardSum (N*(j+1)) n m * W ((N*(j+1) : ℕ) : ℝ)

private theorem modulusSeries_reindex (d : ℕ) [NeZero d]
    (f : Ioi (0 : ℕ) → ℂ) (g : ℕ → ℂ)
    (hzero : ∀ c, ¬ d ∣ c.val → f c = 0)
    (hindex : ∀ j, f (gamma0AtkinSameCuspIndex d j) = g j) :
    (Summable f ↔ Summable g) ∧ (∑' c, f c) = ∑' j, g j := by
  let e := gamma0AtkinSameCuspIndex d
  have hz (c : Ioi (0 : ℕ)) (hc : c ∉ range e) : f c = 0 :=
    hzero c (fun hd => hc ((gamma0AtkinSameCuspIndex_range d c).2 hd))
  have heq : f ∘ e = g := funext hindex
  have hs := (e.injective.summable_iff (f := f) hz).symm
  rw [heq] at hs
  refine ⟨hs, ?_⟩
  have hsupport : Function.support f ⊆ range e := by
    intro c hc
    by_contra h
    exact hc (hz c h)
  calc
    _ = ∑' j, (f ∘ e) j := (e.injective.tsum_eq hsupport).symm
    _ = _ := by rw [heq]

theorem gamma0PeterssonInfinity_modulus_reindex (N : ℕ) [NeZero N] (m n : ℤ) (W : ℝ → ℂ) :
    (Summable (gamma0PeterssonKloostermanModulusTerm N 1 1 m n W) ↔
      Summable (gamma0PeterssonOrdinaryModulusTerm N m n W)) ∧
    (∑' c, gamma0PeterssonKloostermanModulusTerm N 1 1 m n W c) =
      ∑' j, gamma0PeterssonOrdinaryModulusTerm N m n W j := by
  apply modulusSeries_reindex N
  · intro c hc
    dsimp only [gamma0PeterssonKloostermanModulusTerm]
    rw [gamma0TrueWidthKloostermanSum_identity_eq_standard, ite_eq_right hc, zero_mul]
  · intro j
    let _ : NeZero (j+1) := ⟨Nat.succ_ne_zero j⟩
    change gamma0TrueWidthKloostermanSum N 1 1 (N*(j+1)) n m *
        W (gamma0TrueWidthModulus N 1 1 ((N*(j+1) : ℕ) : ℝ)) =
      standardSum (N*(j+1)) n m * W ((N*(j+1) : ℕ) : ℝ)
    rw [gamma0TrueWidthKloostermanSum_identity_eq_standard, ite_eq_left (dvd_mul_right N (j+1))]
    simp only [gamma0TrueWidthModulus, gamma0CuspTrueWidth_identity, Nat.cast_one, Real.sqrt_one, mul_one]

theorem gamma0PeterssonAtkinSameCusp_modulus_reindex (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (m n : ℤ) (W : ℝ → ℂ) :
    let f := gamma0PeterssonKloostermanModulusTerm (r*s) (gamma0CuspOneOver s)
      (gamma0CuspOneOver s) m n W
    let g := gamma0PeterssonOrdinaryModulusTerm (r*s) m n W
    (Summable f ↔ Summable g) ∧
      (∑' c, f c) = atkinPhase (((m : ℝ)-(n : ℝ))*((b : ℝ)/(r : ℝ))) * ∑' j, g j := by
  dsimp only
  let f := gamma0PeterssonKloostermanModulusTerm (r*s) (gamma0CuspOneOver s)
    (gamma0CuspOneOver s) m n W
  let g := gamma0PeterssonOrdinaryModulusTerm (r*s) m n W
  let v := atkinPhase (((m : ℝ)-(n : ℝ))*((b : ℝ)/(r : ℝ)))
  have hv : v ≠ 0 := by
    intro hz
    have hn : ‖v‖ = 1 := atkinPhase_norm _
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  have hzero (c : Ioi (0 : ℕ)) (hc : ¬ s ∣ c.val) : f c = 0 := by
    let _ : NeZero c.val := ⟨c.property.ne'⟩
    dsimp only [f, gamma0PeterssonKloostermanModulusTerm]
    rw [gamma0MixedSameCuspKloosterman_zero_of_not_dvd r s c.val hc n m, zero_mul]
  have hindex (j : ℕ) : f (gamma0AtkinSameCuspIndex s j) = v * g j := by
    let d := j+1
    let _ : NeZero d := ⟨Nat.succ_ne_zero j⟩
    change gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) (s*d) n m *
        W (gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) ((s*d : ℕ) : ℝ)) =
      v * (standardSum ((r*s)*d) n m * W (((r*s)*d : ℕ) : ℝ))
    have hKS : gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s)
        (gamma0CuspOneOver s) (s*d) n m = v * standardSum ((r*s)*d) n m := by
      simpa only [← Nat.mul_assoc, mul_div_assoc, v] using
        gamma0MixedSameCuspKloosterman_eq_standard r s d hcop hab n m
    have hC : gamma0TrueWidthModulus (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s)
        ((s*d : ℕ) : ℝ) = (((r*s)*d : ℕ) : ℝ) := by
      simpa only [← Nat.mul_assoc] using gamma0AtkinSameCusp_modulus r s (s*d) hcop
    rw [hKS, hC, mul_assoc]
  have h := modulusSeries_reindex s f (fun j => v * g j) hzero hindex
  change (Summable f ↔ Summable g) ∧ (∑' c, f c) = v * ∑' j, g j
  exact ⟨h.1.trans (summable_mul_left_iff hv), h.2.trans tsum_mul_left⟩

theorem gamma0PeterssonAtkinSameCusp_modulus_compare (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (m n : ℤ) (W : ℝ → ℂ) :
    let f := gamma0PeterssonKloostermanModulusTerm (r*s) (gamma0CuspOneOver s)
      (gamma0CuspOneOver s) m n W
    let g := gamma0PeterssonKloostermanModulusTerm (r*s) 1 1 m n W
    (Summable f ↔ Summable g) ∧
      (∑' c, f c) = atkinPhase (((m : ℝ)-(n : ℝ))*((b : ℝ)/(r : ℝ))) * ∑' c, g c := by
  dsimp only
  have hAtkin := gamma0PeterssonAtkinSameCusp_modulus_reindex r s hcop hab m n W
  have hInfinity := gamma0PeterssonInfinity_modulus_reindex (r*s) m n W
  exact ⟨hAtkin.1.trans hInfinity.1.symm, hAtkin.2.trans (congrArg _ hInfinity.2.symm)⟩

theorem gamma0PeterssonAtkinSameCusp_positiveModulus_reindex (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (k : ℕ) (m n : ℕ+) :
    let f := gamma0PeterssonPositiveModulusTerm (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) k m n
    let g := gamma0PeterssonPositiveModulusTerm (r*s) 1 1 k m n
    (Summable f ↔ Summable g) ∧
      (∑' c, f c) = atkinPhase (((m : ℝ)-(n : ℝ))*((b : ℝ)/(r : ℝ))) * ∑' c, g c := by
  let W (C : ℝ) : ℂ := (2*(Real.pi : ℂ)*Complex.I^(-(k : ℤ))/(C : ℂ)) *
    ((Real.sqrt ((n : ℝ)/(m : ℝ)) : ℝ) : ℂ)^(k-1) *
    Complex.besselJ ((k-1 : ℕ) : ℂ) (spectralPeterssonBesselArgument m n C : ℂ)
  have he (b a : SL(2, ℤ)) :
      gamma0PeterssonKloostermanModulusTerm (r*s) b a (m : ℤ) (n : ℤ) W =
        gamma0PeterssonPositiveModulusTerm (r*s) b a k m n := by
    funext c
    simp only [gamma0PeterssonKloostermanModulusTerm, gamma0PeterssonPositiveModulusTerm, W]
    ring
  simpa only [he, Int.cast_natCast] using
    gamma0PeterssonAtkinSameCusp_modulus_compare r s hcop hab (m : ℤ) (n : ℤ) W

theorem gamma0PeterssonAtkinSameCusp_gramModulus_reindex (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b = 1)
    (k : ℕ) (m n : ℕ+) :
    let f := gamma0PeterssonGramModulusTerm (r*s) (gamma0CuspOneOver s) (gamma0CuspOneOver s) k m n
    let g := gamma0PeterssonGramModulusTerm (r*s) 1 1 k m n
    (Summable f ↔ Summable g) ∧
      (∑' c, f c) = atkinPhase (((m : ℝ)-(n : ℝ))*((b : ℝ)/(r : ℝ))) * ∑' c, g c := by
  let W (C : ℝ) : ℂ := (2*(Real.pi : ℂ)*Complex.I^(-(k : ℤ))/(C : ℂ)) *
    Complex.besselJ ((k-1 : ℕ) : ℂ) (spectralPeterssonBesselArgument m n C : ℂ)
  have he (b a : SL(2, ℤ)) :
      gamma0PeterssonKloostermanModulusTerm (r*s) b a (m : ℤ) (n : ℤ) W =
        gamma0PeterssonGramModulusTerm (r*s) b a k m n := by
    funext c
    simp only [gamma0PeterssonKloostermanModulusTerm, gamma0PeterssonGramModulusTerm, W, mul_assoc]
  simpa only [he, Int.cast_natCast] using
    gamma0PeterssonAtkinSameCusp_modulus_compare r s hcop hab (m : ℤ) (n : ℤ) W

end ArtinMatthews
