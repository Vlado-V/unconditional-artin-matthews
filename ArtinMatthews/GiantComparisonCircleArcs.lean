module

public import ArtinMatthews.MarkedMinorArcEndpoints
public import ArtinMatthews.GiantComparisonCircleCauchy
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A finite real cover of the literal reduced rational arcs and the
corresponding left-polynomial energy bound. -/
namespace ArtinMatthews
open MeasureTheory AddCircle Set
open scoped BigOperators ComplexConjugate
noncomputable section
local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

local notation "Circle1" => AddCircle (1:ℝ)
local notation "haar" => @AddCircle.haarAddCircle (1:ℝ) _
local notation "unitMeasure" => volume.restrict (Ioc (0:ℝ) 1)

/-- Real intervals around a finite set of rational centers. -/
def giantComparisonArcUnion (C : Finset ℚ) (ρ : ℝ) : Set ℝ :=
  ⋃ r ∈ C, Icc ((r:ℝ)-ρ) ((r:ℝ)+ρ)

theorem giantComparisonArcUnion_measurableSet (C : Finset ℚ) (ρ : ℝ) :
    MeasurableSet (giantComparisonArcUnion C ρ) :=
  C.measurableSet_biUnion fun _ _ => measurableSet_Icc

/-- Overlapping arcs are bounded by the sum of their full-interval energies. -/
theorem giantComparisonArcUnion_energy_le (S : Finset ℤ) (U : S → ℂ)
    (C : Finset ℚ) (ρ δarc : ℝ)
    (henergy : ∀ r ∈ C, (∫ t in Icc ((r:ℝ)-ρ) ((r:ℝ)+ρ),
        ‖markedProductFourierPolynomial S U (t:Circle1)‖^2) ≤ δarc) :
    (∫ t in giantComparisonArcUnion C ρ, ‖markedProductFourierPolynomial S U (t:Circle1)‖^2
      ∂unitMeasure) ≤ (C.card:ℝ)*δarc := by
  let A (r : ℚ) := Icc ((r:ℝ)-ρ) ((r:ℝ)+ρ)
  let F (t : ℝ) := ‖markedProductFourierPolynomial S U (t:Circle1)‖^2
  have hF : Continuous F :=
    (((markedProductFourierPolynomial S U).continuous.comp
      (AddCircle.continuous_mk' (1:ℝ))).norm.pow 2)
  have hI : Integrable F unitMeasure := hF.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hA (r : ℚ) : MeasurableSet (A r) := measurableSet_Icc
  have hi (r : ℚ) : Integrable ((A r).indicator F) unitMeasure :=
    hI.indicator (hA r)
  have hnonneg (r : ℚ) (t : ℝ) : 0 ≤ (A r).indicator F t := by
    by_cases ht : t ∈ A r
    · rw [indicator_of_mem ht]
      exact sq_nonneg _
    · rw [indicator_of_notMem ht]
  have hpoint (t : ℝ) : (giantComparisonArcUnion C ρ).indicator F t ≤
      ∑ r ∈ C, (A r).indicator F t := by
    by_cases ht : t ∈ giantComparisonArcUnion C ρ
    · obtain ⟨r,hr,htr⟩ := mem_iUnion₂.mp ht
      rw [indicator_of_mem ht,← indicator_of_mem (f := F) htr]
      exact Finset.single_le_sum (fun r _ => hnonneg r t) hr
    · rw [indicator_of_notMem ht]
      exact Finset.sum_nonneg fun r _ => hnonneg r t
  rw [← integral_indicator (giantComparisonArcUnion_measurableSet C ρ)]
  calc
    _ ≤ ∫ t, ∑ r ∈ C, (A r).indicator F t ∂unitMeasure :=
      integral_mono (hI.indicator (giantComparisonArcUnion_measurableSet C ρ))
        (integrable_finsetSum C (fun r _ => hi r)) hpoint
    _ = ∑ r ∈ C, ∫ t in A r, F t ∂unitMeasure := by
      rw [integral_finsetSum C (fun r _ => hi r)]
      apply Finset.sum_congr rfl
      intro r _
      exact integral_indicator (hA r)
    _ ≤ ∑ r ∈ C, δarc := by
      apply Finset.sum_le_sum
      intro r hr
      calc
        _ ≤ ∫ t in A r, F t := integral_mono_measure
          (Measure.restrict_mono Subset.rfl Measure.restrict_le_self)
          (Filter.Eventually.of_forall fun _ => sq_nonneg _) hF.integrableOn_Icc
        _ ≤ _ := henergy r hr
    _ = _ := by simp

/-- The finite reduced rational centers sufficient on the unit cell for
radii at most one. Integer translates meeting the cell remain included. -/
def giantComparisonRationalCenters (Q : ℝ) : Finset ℚ :=
  let q := ⌊Q⌋₊
  (((Finset.Icc (-(q:ℤ)) (2*(q:ℤ))) ×ˢ (Finset.Icc 1 q)).image
    (fun ab : ℤ×ℕ => (ab.1:ℚ)/(ab.2:ℚ))).filter (fun r => (r.den:ℝ) ≤ Q)

theorem giantComparisonRationalCenters_den_le {Q : ℝ} {r : ℚ}
    (hr : r ∈ giantComparisonRationalCenters Q) : (r.den:ℝ) ≤ Q :=
  (Finset.mem_filter.mp hr).2

theorem giantComparisonRationalCenters_cover {θ Q ρ : ℝ}
    (hθ : θ ∈ Ioc (0:ℝ) 1) (hρ : ρ ≤ 1) :
    θ ∈ giantComparisonArcUnion (giantComparisonRationalCenters Q) ρ ↔
      MarkedInRationalArc θ Q ρ := by
  constructor
  · intro h
    obtain ⟨r,hr,htr⟩ := mem_iUnion₂.mp h
    exact ⟨r,giantComparisonRationalCenters_den_le hr,abs_le.mpr
      ⟨by linarith [htr.1],by linarith [htr.2]⟩⟩
  · rintro ⟨r,hrQ,hr⟩
    have hden : r.den ≤ ⌊Q⌋₊ := (Nat.le_floor_iff' r.pos.ne').mpr hrQ
    have hden0 : (0:ℝ) < r.den := by exact_mod_cast r.pos
    have hlo : -1 ≤ (r:ℝ) := by linarith [(abs_le.mp hr).2,hθ.1]
    have hhi : (r:ℝ) ≤ 2 := by linarith [(abs_le.mp hr).1,hθ.2]
    rw [Rat.cast_def] at hlo hhi
    have hnumlo : -(r.den:ℤ) ≤ r.num := by
      have h := (le_div_iff₀ hden0).mp hlo
      exact_mod_cast (show -(r.den:ℝ) ≤ (r.num:ℝ) by simpa only [neg_mul,one_mul] using h)
    have hnumhi : r.num ≤ 2*(r.den:ℤ) := by
      exact_mod_cast (div_le_iff₀ hden0).mp hhi
    apply mem_iUnion₂.mpr
    refine ⟨r,?_,⟨by linarith [(abs_le.mp hr).1],by linarith [(abs_le.mp hr).2]⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(r.num,r.den),?_,Rat.num_div_den r⟩,hrQ⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,Finset.mem_Icc.mpr ⟨r.pos,hden⟩⟩

theorem giantComparisonRationalCenters_card_le_floor (Q : ℝ) :
    (giantComparisonRationalCenters Q).card ≤ (3*⌊Q⌋₊+1)*⌊Q⌋₊ := by
  let q := ⌊Q⌋₊
  let A := Finset.Icc (-(q:ℤ)) (2*(q:ℤ))
  let B := Finset.Icc 1 q
  have hA : A.card = 3*q+1 := by
    dsimp only [A]
    rw [Int.card_Icc]
    omega
  have hB : B.card = q := by
    dsimp only [B]
    rw [Nat.card_Icc]
    omega
  unfold giantComparisonRationalCenters
  change (((A ×ˢ B).image (fun ab : ℤ×ℕ => (ab.1:ℚ)/(ab.2:ℚ))).filter
      (fun r => (r.den:ℝ) ≤ Q)).card ≤ (3*q+1)*q
  exact (Finset.card_filter_le _ _).trans
    (Finset.card_image_le.trans (by rw [Finset.card_product,hA,hB]))

theorem giantComparisonRationalCenters_card_le {Q : ℝ} (hQ : 1 ≤ Q) :
    ((giantComparisonRationalCenters Q).card:ℝ) ≤ 4*Q^2 := by
  have hfloor : (⌊Q⌋₊:ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hfloor0 : (0:ℝ) ≤ ⌊Q⌋₊ := Nat.cast_nonneg _
  have hcard : ((giantComparisonRationalCenters Q).card:ℝ) ≤
      (3*(⌊Q⌋₊:ℝ)+1)*(⌊Q⌋₊:ℝ) := by
    exact_mod_cast giantComparisonRationalCenters_card_le_floor Q
  calc
    _ ≤ _ := hcard
    _ ≤ (4*Q)*Q := mul_le_mul (by linarith) hfloor hfloor0 (by positivity)
    _ = _ := by ring

/-- The arcs are invariant under reflection of the real representative. -/
theorem markedInRationalArc_neg_iff {θ Q ρ : ℝ} :
    MarkedInRationalArc (-θ) Q ρ ↔ MarkedInRationalArc θ Q ρ := by
  have reflect (x : ℝ) : MarkedInRationalArc x Q ρ → MarkedInRationalArc (-x) Q ρ := by
    rintro ⟨r,hr,hx⟩
    refine ⟨-r,by simpa only [Rat.den_neg_eq_den] using hr,?_⟩
    rw [Rat.cast_neg,show -x-(-(r:ℝ)) = -(x-(r:ℝ)) by ring,abs_neg]
    exact hx
  exact ⟨fun h => by simpa only [neg_neg] using reflect (-θ) h,reflect θ⟩

/-- Major/minor estimate for the actual rational arcs on the unit circle.
The major contribution uses only the local left-polynomial energy. -/
theorem giantComparisonCircle_rational_major_minor_bound
    (m : Circle1 → ℂ) (hm : Continuous m) (S T : Finset ℤ) (U : S → ℂ) (V : T → ℂ)
    {Q ρ δ δarc : ℝ} (hQ : 1 ≤ Q) (hρ : ρ ≤ 1) (hδ : 0 ≤ δ) (hδarc : 0 ≤ δarc)
    (hunit : ∀ θ, ‖m θ‖ ≤ 1)
    (hminor : ∀ t ∈ Ioc (0:ℝ) 1, ¬MarkedInRationalArc t Q ρ → ‖m (t:Circle1)‖ ≤ δ)
    (henergy : ∀ r : ℚ, (r.den:ℝ) ≤ Q →
      (∫ t in Icc ((r:ℝ)-ρ) ((r:ℝ)+ρ), ‖markedProductFourierPolynomial S U (t:Circle1)‖^2)
        ≤ δarc) :
    ‖∫ θ : Circle1, m θ*conj (markedProductFourierPolynomial S U θ)*
        markedProductFourierPolynomial T V θ ∂haar‖ ≤
      δ*Real.sqrt ((∑ u : S, ‖U u‖^2)*(∑ v : T, ‖V v‖^2)) +
        Real.sqrt ((∑ v : T, ‖V v‖^2)*(4*Q^2*δarc)) := by
  let C := giantComparisonRationalCenters Q
  apply giantComparisonCircle_major_minor_bound m hm S T U V (giantComparisonArcUnion C ρ)
    (giantComparisonArcUnion_measurableSet C ρ) hδ hunit
  · intro t ht h
    exact hminor t ht (fun hr => h ((giantComparisonRationalCenters_cover ht hρ).mpr hr))
  · exact (giantComparisonArcUnion_energy_le S U C ρ δarc (fun r hr =>
      henergy r (giantComparisonRationalCenters_den_le hr))).trans
        (mul_le_mul_of_nonneg_right (giantComparisonRationalCenters_card_le hQ) hδarc)

end
end ArtinMatthews
