module

public import ArtinMatthews.SourceReflectionSeries
public import ArtinMatthews.SourceReflectionColumnSieve
public import ArtinMatthews.SourceReflectionDyadicIndex
public import ArtinMatthews.SourceReflectionIdealCutoffs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The retained branch is a literal finite sum. It retains the original
joint length cutoff even after splitting the column norm dyads. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {U : Type} (A : SourceReflectionExpansionData F S₀ U)

local notation "Prime" => SourceExteriorPrime F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

def sourceReflectionRetainedNumerators (f : Finset Prime) (R : ℝ) :
    Finset (SourceReflectionFrozenNumerator F S₀ f) :=
  (sourceReflectionBoundedExponents F S₀ R).preimage Subtype.val Subtype.val_injective.injOn

def sourceReflectionRetainedCubes (R : ℝ) : Finset E :=
  sourceReflectionBoundedExponents F S₀ (R ^ (1 / 3 : ℝ))

def sourceReflectionRetainedColumns (R : ℝ) : Finset E :=
  (sourceReflectionBoundedExponents F S₀ R).filter sourceReflectionIsSquarefree

def sourceReflectionRetainedColumnDyad (R : ℝ) (j : ℕ) : Finset E :=
  (sourceReflectionRetainedColumns F S₀ R).filter (fun c => Nat.log 2 (q c) = j)

theorem sourceReflectionTermLength_bounds {R : ℝ} {a n c : E}
    (hQ : sourceReflectionTermLength F S₀ a n c ≤ R) :
    (q a : ℝ) ≤ R ∧ (q n : ℝ) ≤ R ^ (1 / 3 : ℝ) ∧ (q c : ℝ) ≤ R := by
  have ha := sourceReflection_norm_one_le F S₀ a
  have hn := sourceReflection_norm_one_le F S₀ n
  have hc := sourceReflection_norm_one_le F S₀ c
  have ha₀ := zero_le_one.trans ha
  have hn₀ := zero_le_one.trans hn
  have hc₀ := zero_le_one.trans hc
  have hQ' := hQ
  unfold sourceReflectionTermLength at hQ'
  have hn₃ : 1 ≤ (q n : ℝ) ^ 3 := one_le_pow₀ hn
  have hac : (q a : ℝ) * (q c : ℝ) ≤ R :=
    (le_mul_of_one_le_right (mul_nonneg ha₀ hc₀) hn₃).trans hQ'
  have hpow : (q n : ℝ) ^ 3 ≤ R :=
    (le_mul_of_one_le_left (pow_nonneg hn₀ _) (one_le_mul_of_one_le_of_one_le ha hc)).trans hQ'
  have hpow' : ((q n : ℝ) ^ 3) ^ (1 / 3 : ℝ) = (q n : ℝ) := by
    rw [← Real.rpow_natCast_mul hn₀]
    norm_num
  exact ⟨(le_mul_of_one_le_right ha₀ hc).trans hac,
    hpow' ▸ Real.rpow_le_rpow (pow_nonneg hn₀ _) hpow (by norm_num),
    (le_mul_of_one_le_left hc₀ ha).trans hac⟩

theorem sourceReflectionRetainedBranch_zero_of_lt_one (Z : ℝ) (h d : E) (f : Finset Prime)
    (u : U) {R : ℝ} (hR : R < 1) :
    sourceReflectionSelectedBranch F S₀ hζ A Z h d f u (fun Q => Q ≤ R) = 0 := by
  have hQ (i : SourceReflectionTermIndex F S₀ f) :
      ¬ sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val ≤ R :=
    not_le.mpr (hR.trans_le (sourceReflectionTermLength_one_le F S₀ _ _ _))
  simp only [sourceReflectionSelectedBranch, ite_eq_right (hQ _), tsum_zero]

theorem sourceReflectionRetainedBranch_eq_sum (Z : ℝ) (h d : E) (f : Finset Prime)
    (u : U) {R : ℝ} (hR : 1 ≤ R) :
    sourceReflectionSelectedBranch F S₀ hζ A Z h d f u (fun Q => Q ≤ R) =
      ∑ a ∈ sourceReflectionRetainedNumerators F S₀ f R,
        ∑ n ∈ sourceReflectionRetainedCubes F S₀ R,
          (A.scalar h f a.val n u / (q n : ℂ)) *
            sourceReflectionColumnBlock F S₀ hζ A Z R h f a.val n u
              (sourceReflectionRetainedColumns F S₀ R) d := by
  let T := sourceReflectionRetainedNumerators F S₀ f R
  let N := sourceReflectionRetainedCubes F S₀ R
  let B := sourceReflectionRetainedColumns F S₀ R
  let C : Finset (ReflectionSquarefreeExponents F S₀) :=
    B.preimage Subtype.val Subtype.val_injective.injOn
  have hR₀ := zero_le_one.trans hR
  have hC : C.image Subtype.val = B := by
    ext c
    constructor
    · intro hc
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_preimage.mp hx
    · intro hc
      have hsf : sourceReflectionIsSquarefree c := (Finset.mem_filter.mp hc).2
      exact Finset.mem_image.mpr ⟨⟨c,hsf⟩, Finset.mem_preimage.mpr hc, rfl⟩
  unfold sourceReflectionSelectedBranch
  rw [tsum_eq_sum (s := T ×ˢ N ×ˢ C)]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro n _
    let k (c : E) :=
      A.row h f a.val n u d * sourceReflectionQuadraticSymbol F S₀ hζ d c *
        (if sourceReflectionTermLength F S₀ a.val n c ≤ R then
          sourceReflectionColumnCoefficient F S₀ A h f a.val n u c else 0) *
        A.profile h f a.val n u (sourceReflectionTermLength F S₀ a.val n c /
          sourceReflectionTermScale F S₀ Z f d)
    let s := A.scalar h f a.val n u / (q n : ℂ)
    have hsum : ∑ c ∈ B, k c = ∑ c ∈ C, k c.val := by
      calc
        _ = ∑ c ∈ C.image (fun c : ReflectionSquarefreeExponents F S₀ => c.val), k c :=
          congrArg (fun X : Finset E => ∑ c ∈ X, k c) hC.symm
        _ = _ := Finset.sum_image (fun x _ y _ hxy => Subtype.ext hxy)
    calc
      _ = ∑ c ∈ C, s * k c.val := by
        apply Finset.sum_congr rfl
        intro c _
        change (if sourceReflectionTermLength F S₀ a.val n c.val ≤ R then
          sourceReflectionExpansionTerm F S₀ hζ A Z h d f a.val n c.val u else 0) = s * k c.val
        by_cases hc : sourceReflectionTermLength F S₀ a.val n c.val ≤ R
        · simp only [ite_eq_left hc, sourceReflectionExpansionTerm, k, s]
        · simp only [ite_eq_right hc, k, mul_zero, zero_mul]
      _ = s * (∑ c ∈ B, k c) := by rw [← Finset.mul_sum, hsum]
      _ = _ := rfl
  · intro i hi
    apply ite_eq_right
    intro hQ
    obtain ⟨ha, hn, hc⟩ := sourceReflectionTermLength_bounds F S₀ hQ
    apply hi
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_preimage.mpr ((sourceReflection_mem_boundedExponents F S₀ hR₀ _).2 ha), ?_⟩
    apply Finset.mem_product.mpr
    exact ⟨(sourceReflection_mem_boundedExponents F S₀ (Real.rpow_nonneg hR₀ _) _).2 hn,
      Finset.mem_preimage.mpr (Finset.mem_filter.mpr
        ⟨(sourceReflection_mem_boundedExponents F S₀ hR₀ _).2 hc, i.2.2.property⟩)⟩

theorem sourceReflectionColumnBlock_sum_dyads (Z : ℝ) {R : ℝ} (hR : 1 ≤ R)
    (h : E) (f : Finset Prime) (a n : E) (u : U) (d : E) :
    sourceReflectionColumnBlock F S₀ hζ A Z R h f a n u (sourceReflectionRetainedColumns F S₀ R) d =
      ∑ j ∈ Finset.range (sourceReflectionDyadLength R),
        sourceReflectionColumnBlock F S₀ hζ A Z R h f a n u
          (sourceReflectionRetainedColumnDyad F S₀ R j) d := by
  unfold sourceReflectionColumnBlock sourceReflectionRetainedColumnDyad
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro c hc
  have h := (sourceReflection_mem_boundedExponents F S₀ (zero_le_one.trans hR) c).mp
    (Finset.mem_filter.mp hc).1
  exact Finset.mem_range.mpr (sourceReflectionDyad_lt_length h)

end
end ArtinMatthews.SourceEulerAssembly
