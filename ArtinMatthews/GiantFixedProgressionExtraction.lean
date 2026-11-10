module

public import ArtinMatthews.GiantFixedProgressionExtractionFinite
public import ArtinMatthews.GiantFixedProgressionRough
public import ArtinMatthews.GiantPrimeExtractionComposition
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual fixed-progression rough bound transfers to the normalized
marked prime sum once the literal composite tuples cancel. The sieve error
is the exact fixed-progression density times the original depth error. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Asymptotics Classical
noncomputable section

theorem giantFixedProgressionExtractionRough_eq_raw_eventually {M : ℕ}
    (U : Finset (ZMod M)ˣ) {J : Type*} [Fintype J] (e : J → ℝ)
    (ε γ : ℝ) (hε : ε≤1/4) (Φ : ℝ → ℝ) {T : ℝ} (hT : 0≤T) (hΦzero : Φ 0=0)
    (hhigh : ∀ t,T<t → Φ t=0) :
    ∀ᶠ x : ℝ in atTop,
      giantFixedProgressionExtractionRough U e (giantMarkedCenteredCore ε) Φ (T+1) γ x =
        giantFixedProgressionArrayRoughRaw U e ε Φ T x γ := by
  filter_upwards [giantFixedProgressionExtraction_weight_eq_literal_eventually U e ε hε Φ hT hΦzero,
    eventually_ge_atTop (1:ℝ)] with x hl hx
  rw [giantFixedProgressionExtractionRough_eq_predecessor U e _ Φ γ hT hx hhigh]
  unfold giantFixedProgressionArrayRoughRaw
  exact sum_congr rfl (fun u hu => hl u (mem_filter.mp hu).1)

theorem giant_fixed_progression_extraction_prime_sub_rough_isLittleO_of_tuple {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,0<e j)
    (G : ℝ → ℕ → ℂ) {CG : ℝ} (hCG : 0≤CG) (hG : ∀ᶠ x : ℝ in atTop,∀ u,‖G x u‖≤CG)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {a b T γ : ℝ} (ha : 0<a)
    (hsupp : Function.support Φ ⊆ Set.Icc a b) (hT : 0≤T) (hγ : 0<γ) (hγ1 : γ<1)
    (htuple : ∀ (χ : DirichletCharacter ℂ M) j, j∈Icc 2 ⌈2/γ⌉₊ →
      giantOrdinaryTupleSum e χ G Φ T γ j =o[atTop] (fun x : ℝ => x/Real.log x)) :
    (fun x => giantFixedProgressionExtractionPrime U e G Φ T x -
      giantFixedProgressionExtractionRough U e G Φ T γ x) =o[atTop]
      (fun x : ℝ => x/Real.log x) := by
  have heq (x : ℝ) : x*(Real.log x)^(-(1:ℝ)) = x/Real.log x := by
    rw [Real.rpow_neg_one,div_eq_mul_inv]
  have hχ (χ : DirichletCharacter ℂ M) :
      (fun x => giantOrdinaryPrimeSum e χ G Φ T x-giantOrdinaryRoughSum e χ G Φ T γ x)
        =o[atTop] (fun x : ℝ => x/Real.log x) := by
    have h := giant_ordinary_prime_sub_rough_isLittleO_of_tuple e he χ G hCG hG Φ hΦ ha
      hsupp hT hγ hγ1 1 (fun j hj => by simpa only [heq] using htuple χ j hj)
    simpa only [heq] using h
  apply (Asymptotics.IsLittleO.sum (s:=Finset.univ)
    (fun χ (_ : χ∈(Finset.univ:Finset (DirichletCharacter ℂ M))) =>
      (hχ χ).const_mul_left (giantResidueCharacterCoefficient U χ))).congr' _
    Filter.EventuallyEq.rfl
  filter_upwards [] with x
  simp only [Finset.sum_apply,giantFixedProgressionExtractionPrime_eq_character_sum,
    giantFixedProgressionExtractionRough_eq_character_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun χ _ => mul_sub _ _ _)

theorem giant_fixed_progression_marked_prime_bound_of_tuple {M : ℕ} [NeZero M]
    (U : Finset (ZMod M)ˣ) {J : Type*} [Fintype J] [DecidableEq J] (e : J → ℝ)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<1/5) (hinj : Function.Injective e)
    (ε c : ℝ) (m : ℕ) (hε : 0<ε) (hεq : ε<1/4) (hc : 0<c) (hcε : c<ε/2)
    (hm : 20000 ≤ m) (Φ : ℝ → ℝ) {a T : ℝ}
    (ha : 0<a) (hT : 0≤T) (hΦ : Differentiable ℝ Φ) (hderiv : Continuous (deriv Φ))
    (hsupp : Function.support Φ ⊆ Set.Ioo a T) (hΦ0 : ∀ t,0≤Φ t)
    (htuple : ∀ (χ : DirichletCharacter ℂ M) j, j∈Icc 2 ⌈2/markedSieveExponent c m⌉₊ →
      giantOrdinaryTupleSum e χ (giantMarkedCenteredCore ε) Φ (T+1) (markedSieveExponent c m) j
        =o[atTop] (fun x : ℝ => x/Real.log x)) :
    ∀ η : ℝ, 0<η → ∀ᶠ x : ℝ in atTop,
      Real.log x/x*‖giantFixedProgressionArrayPrimeSum U e ε Φ T x‖ ≤
        (U.card:ℝ)*giantFixedResidueRoughError M Φ T c m+η := by
  let γ := markedSieveExponent c m
  let G := giantMarkedCenteredCore ε
  let P := giantFixedProgressionExtractionPrime U e G Φ (T+1)
  let R := giantFixedProgressionExtractionRough U e G Φ (T+1) γ
  let E := (U.card:ℝ)*giantFixedResidueRoughError M Φ T c m
  have he0 : ∀ j,0<e j := fun j => lt_trans (by norm_num) (he j).1
  have hγ : 0<γ := markedSieveExponent_pos hc m
  have hγ1 : γ<1 := by
    unfold γ markedSieveExponent
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) m]
  have hΦzero : Φ 0=0 := by
    by_contra h
    exact (not_lt_of_ge ha.le) (hsupp h).1
  have hΦT : Φ T=0 := by
    by_contra h
    exact (lt_irrefl T) (hsupp h).2
  have hhigh (t : ℝ) (ht : T<t) : Φ t=0 := by
    by_contra h
    exact (not_lt_of_ge ht.le) (hsupp h).2
  have hG : ∀ᶠ x : ℝ in atTop,∀ u,‖G x u‖≤1 :=
    (giantMarkedCenteredCore_interface e (fun j => (he j).2.trans (by norm_num)) hε hεq).mono
      (fun _ h => h.1)
  have hdiff : (fun x => P x-R x) =o[atTop] (fun x : ℝ => x/Real.log x) :=
    giant_fixed_progression_extraction_prime_sub_rough_isLittleO_of_tuple U e he0 G zero_le_one hG
      Φ hΦ.continuous ha (fun _ h => ⟨(hsupp h).1.le,(hsupp h).2.le⟩)
      (show 0≤T+1 by linarith) hγ hγ1 htuple
  have hR : ∀ η : ℝ,0<η → ∀ᶠ x : ℝ in atTop,
      Real.log x/(x*literalMarkedArrayMean e x)*‖R x‖≤E+η := by
    intro η hη
    filter_upwards [giant_fixed_progression_array_rough_bound U e he hinj ε c m hε hεq hc hcε hm
        Φ hT hΦ hderiv hΦT hΦ0 hΦzero hη,
      giantFixedProgressionExtractionRough_eq_raw_eventually U e ε γ hεq.le Φ hT hΦzero hhigh]
      with x hx heq
    change Real.log x/(x*literalMarkedArrayMean e x)*
      ‖giantFixedProgressionExtractionRough U e G Φ (T+1) γ x‖ ≤ _
    rw [heq]
    exact hx
  have hP := giant_normalized_bound_transfer P R (literalMarkedArrayMean e)
    (show 0<(1/2:ℝ)^Fintype.card J by positivity)
    (literalMarkedArrayMean_lower_eventually e he0) hdiff E hR
  intro η hη
  filter_upwards [hP η hη,
    giantFixedProgressionExtractionPrime_div_eq_array_eventually U e ε hεq.le Φ hT hΦzero hhigh,
    literalMarkedArrayMean_lower_eventually e he0] with x hp hpx hmean
  have hmpos : 0<literalMarkedArrayMean e x := (by positivity : 0<(1/2:ℝ)^Fintype.card J).trans_le hmean
  rw [← hpx,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hmpos]
  calc
    _ = Real.log x/(x*literalMarkedArrayMean e x)*‖P x‖ := by dsimp only [P]; ring
    _ ≤ _ := hp

end
end ArtinMatthews
