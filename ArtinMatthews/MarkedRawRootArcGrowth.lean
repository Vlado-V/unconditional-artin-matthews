module

public import ArtinMatthews.MarkedMinorArcDirtySecondGood
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Elementary size and counting bounds for the actual frequencies in
the first and beta root tests. These use the prime-band endpoints, not
a hypothesized bound on the trial integers. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators

theorem markedRootArc_band_prime_le {β b x : ℝ} (hlog : 1 ≤ Real.log x) (hb : b ≤ β)
    {p : ℕ} (hp : p ∈ markedLogPowerBand b x) :
    (p:ℝ) ≤ Real.exp (2*(Real.log x)^β) := by
  exact (mem_markedLogPowerBand.mp hp).2.2.trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog hb) (by norm_num)))

theorem markedRootArc_tuple_product_le {I : Type*} [Fintype I]
    (b : I → ℝ) {β x : ℝ} (hlog : 1 ≤ Real.log x) (hb : ∀ i,b i ≤ β)
    (p : MarkedTrialPrimeChoices b x) :
    ((∏ i,(p i:ℕ):ℕ):ℝ) ≤ Real.exp (2*(Fintype.card I:ℝ)*(Real.log x)^β) := by
  calc
    _ = ∏ i,((p i:ℕ):ℝ) := by simp
    _ ≤ ∏ _i : I,Real.exp (2*(Real.log x)^β) := by
      exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => markedRootArc_band_prime_le hlog (hb i) (p i).2)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,← Real.exp_nat_mul]; congr 1; ring

theorem markedRootArc_full_product_le {J : Type*} [Fintype J]
    (e : J → ℝ) {β x : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    {M : ℕ} (source : MarkedRawActive (markedRawActualPrimeBand e x) M) :
    (markedSourceFullProduct (markedRawNumericActive source):ℝ) ≤
      Real.exp (2*(Fintype.card J:ℝ)*M*(Real.log x)^β) := by
  have hs (j : J) (k : Fin M) : (markedRawNumericActive source j k:ℝ) ≤
      Real.exp (2*(Real.log x)^β) := by
    apply markedRootArc_band_prime_le hlog (he j)
    exact (mem_markedRawPrimeBand _ (source j k).1).mp (source j k).2
  calc
    _ = ∏ j,∏ k,(markedRawNumericActive source j k:ℝ) := by simp [markedSourceFullProduct]
    _ ≤ ∏ _j : J,∏ _k : Fin M,Real.exp (2*(Real.log x)^β) := by
      apply Finset.prod_le_prod₀ (fun j _ => Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _))
      intro j _
      exact Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun k _ => hs j k)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul]; congr 1; ring

theorem markedRootArc_copied_product_le {J : Type*} [Fintype J]
    (e : J → ℝ) {β x : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    {M : ℕ} (source : MarkedRawActive (markedRawActualPrimeBand e x) M) (o : J → Fin M) :
    (markedSourceCopiedProduct (markedRawNumericActive source) o:ℝ) ≤
      Real.exp (2*(Fintype.card J:ℝ)*M*(Real.log x)^β) := by
  have hp : 0 < markedSourceFullProduct (markedRawNumericActive source) :=
    Finset.prod_pos (fun j _ => Finset.prod_pos (fun k _ => (source j k).1.2.pos))
  exact (Nat.cast_le.mpr (Nat.le_of_dvd hp
    (markedSourceCopied_dvd_full (markedRawNumericActive source) o))).trans
      (markedRootArc_full_product_le e hlog he source)

theorem markedRootArc_trial_abs_le {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {β x : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    {M : ℕ} (source : MarkedRawActive (markedRawActualPrimeBand e x) M)
    (I : Finset J) {u : ℤ} (hu : u ∈ markedRawDirtyFullTrials e x source I) :
    |(u:ℝ)| ≤ Real.exp (2*(Fintype.card J:ℝ)*(M+1)*(Real.log x)^β) := by
  obtain ⟨⟨o,p⟩,_,rfl⟩ := Finset.mem_image.mp hu
  have hp := markedRootArc_tuple_product_le (fun j : I => e j.1) hlog (fun j => he j.1) p
  have hcard : (Fintype.card I:ℝ) ≤ Fintype.card J := by
    exact_mod_cast (show Fintype.card I ≤ Fintype.card J by simpa only [Fintype.card_coe] using I.card_le_univ)
  have hp' : ((∏ j : I,(p j:ℕ):ℕ):ℝ) ≤ Real.exp (2*(Fintype.card J:ℝ)*(Real.log x)^β) :=
    hp.trans (Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg (zero_le_one.trans hlog) β]))
  calc
    _ = (markedSourceCopiedProduct (markedRawNumericActive source) o:ℝ)*((∏ j : I,(p j:ℕ):ℕ):ℝ) := by
      push_cast
      rw [abs_of_nonneg (by positivity)]
    _ ≤ Real.exp (2*(Fintype.card J:ℝ)*M*(Real.log x)^β)*
        Real.exp (2*(Fintype.card J:ℝ)*(Real.log x)^β) :=
      mul_le_mul (markedRootArc_copied_product_le e hlog he source o) hp' (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem markedRootArc_trial_card_le {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) {β x : ℝ} (hlog : 1 ≤ Real.log x) (he : ∀ j,e j ≤ β)
    {M : ℕ} (source : MarkedRawActive (markedRawActualPrimeBand e x) M) (I : Finset J) :
    ((markedRawDirtyFullTrials e x source I).card:ℝ) ≤
      (M:ℝ)^(Fintype.card J)*Real.exp (2*(Fintype.card J:ℝ)*(Real.log x)^β) := by
  have hc : (markedRawDirtyFullTrials e x source I).card ≤
      M^(Fintype.card J)*∏ j : I,(markedLogPowerBand (e j.1) x).card := by
    simpa only [markedRawDirtyFullTrials,Finset.card_univ,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
      MarkedTrialPrimeChoices,Fintype.card_pi,Fintype.card_coe] using
      (Finset.card_image_le (s := Finset.univ)
        (f := fun c : (J → Fin M) × MarkedTrialPrimeChoices (fun j : I => e j.1) x =>
          ((markedSourceCopiedProduct (markedRawNumericActive source) c.1*∏ j : I,(c.2 j:ℕ):ℕ):ℤ)))
  have hp : (∏ j : I,((markedLogPowerBand (e j.1) x).card:ℝ)) ≤
      Real.exp (2*(Fintype.card I:ℝ)*(Real.log x)^β) := by
    calc
      _ ≤ ∏ _j : I,Real.exp (2*(Real.log x)^β) := by
        apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro j _
        exact (markedBand_card_le_exp (e j.1) x).trans (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlog (he j.1)) (by norm_num)))
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ,← Real.exp_nat_mul]; congr 1; ring
  have hcard : (Fintype.card I:ℝ) ≤ Fintype.card J := by
    exact_mod_cast (show Fintype.card I ≤ Fintype.card J by simpa only [Fintype.card_coe] using I.card_le_univ)
  have hc' : ((markedRawDirtyFullTrials e x source I).card:ℝ) ≤
      (M:ℝ)^(Fintype.card J)*∏ j : I,((markedLogPowerBand (e j.1) x).card:ℝ) := by exact_mod_cast hc
  apply hc'.trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
  exact hp.trans (Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg (zero_le_one.trans hlog) β]))

end
end ArtinMatthews
