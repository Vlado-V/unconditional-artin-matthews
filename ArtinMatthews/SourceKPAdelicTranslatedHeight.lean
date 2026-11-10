module

public import ArtinMatthews.SourceKPAdelicHeight
public import ArtinMatthews.SourceArchMatrixHeight
public import Mathlib.NumberTheory.Height.NumberField
public import ArtinMatthews.SourceKPAdelicCompactIntersection
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

/-! Actual adelic right-translation constants and rational height comparison. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup Filter
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicOpenCellMatrix (x : K) : GL (Fin 2) 𝔸[K] :=
  sourceKPWeylMatrix 𝔸[K] * sourceKPUpperMatrix 𝔸[K] (algebraMap K 𝔸[K] x)

theorem sourceKPAdelicOpenCellMatrix_finite (x : K) (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdelicBaseFiniteAt K P (sourceKPAdelicOpenCellMatrix K x) =
      sourceGL2Weyl * sourceGL2Upper (algebraMap K (P.adicCompletion K) x) := by
  let φ := (sourceKPAdeleEval K P).comp (sourceKPAdeleFiniteProjection K)
  have he (g : GL (Fin 2) 𝔸[K]) : sourceKPAdelicBaseFiniteAt K P g = GeneralLinearGroup.map φ g := by
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  rw [he, sourceKPAdelicOpenCellMatrix, map_mul, sourceKPWeylMatrix_map,
    sourceKPUpperMatrix_map, sourceKPWeylMatrix_field, sourceKPUpperMatrix_field]
  rfl

theorem sourceKPAdelicOpenCellMatrix_complex (x : K) (v : InfinitePlace K) :
    sourceKPAdelicBaseComplexAt K hζ v (sourceKPAdelicOpenCellMatrix K x) =
      sourceGL2Weyl * sourceGL2Upper
        (sourceKPArchComplexEquiv K hζ v (algebraMap K v.Completion x)) := by
  let φ := (sourceKPArchComplexEquiv K hζ v).toRingHom.comp
    ((sourceArchAdeleEval K v).comp (sourceKPAdeleInfiniteProjection K))
  have he (g : GL (Fin 2) 𝔸[K]) : sourceKPAdelicBaseComplexAt K hζ v g = GeneralLinearGroup.map φ g := by
    apply GeneralLinearGroup.ext
    intro i j
    rfl
  rw [he, sourceKPAdelicOpenCellMatrix, map_mul, sourceKPWeylMatrix_map,
    sourceKPUpperMatrix_map, sourceKPWeylMatrix_field, sourceKPUpperMatrix_field]
  rfl

theorem sourceKPAdelicFiniteHeight_finite_support (g : GL (Fin 2) 𝔸[K]) :
    (fun P : HeightOneSpectrum (𝓞 K) =>
      sourceKPFiniteMatrixHeight K P (sourceKPAdelicBaseFiniteAt K P g)).HasFiniteMulSupport := by
  apply Filter.eventually_cofinite.mp
  exact (sourceKPAdeleMatrixAt_eventually_integral K (sourceKPGL2ProductEquiv K g).2).mono
    (fun P hP => sourceKPFiniteMatrixHeight_integral K P _ hP)

theorem sourceKPAdelicHeightConstant_finite_support (g : GL (Fin 2) 𝔸[K]) :
    (fun P : HeightOneSpectrum (𝓞 K) =>
      sourceKPFiniteMatrixHeightConstant K P (sourceKPAdelicBaseFiniteAt K P g)).HasFiniteMulSupport := by
  apply Filter.eventually_cofinite.mp
  exact (sourceKPAdeleMatrixAt_eventually_integral K (sourceKPGL2ProductEquiv K g).2).mono
    (fun P hP => sourceKPFiniteMatrixHeightConstant_integral K P _ hP)

def sourceKPAdelicHeightConstant (g : GL (Fin 2) 𝔸[K]) : ℝ :=
  (∏ v : InfinitePlace K, sourceArchMatrixHeightConstant (sourceKPAdelicBaseComplexAt K hζ v g) ^ v.mult) *
    ∏ᶠ P : HeightOneSpectrum (𝓞 K),
      sourceKPFiniteMatrixHeightConstant K P (sourceKPAdelicBaseFiniteAt K P g)

theorem sourceKPAdelicHeightConstant_pos (g : GL (Fin 2) 𝔸[K]) :
    0 < sourceKPAdelicHeightConstant K hζ g := by
  unfold sourceKPAdelicHeightConstant
  apply mul_pos
  · exact Finset.prod_pos (fun v _ => pow_pos (sourceArchMatrixHeightConstant_pos _) _)
  · rw [finprod_eq_prod _ (sourceKPAdelicHeightConstant_finite_support K g)]
    exact Finset.prod_pos (fun P _ => sourceKPFiniteMatrixHeightConstant_pos K P _)

theorem sourceKPRationalFiniteMax_finite_support (x : K) :
    (fun P : HeightOneSpectrum (𝓞 K) => max 1 ‖algebraMap K (P.adicCompletion K) x‖).HasFiniteMulSupport := by
  apply Filter.eventually_cofinite.mp
  filter_upwards [FiniteAdeleRing.cofinite_mem_adicCompletionIntegers
    ((algebraMap K 𝔸[K] x).2)] with P hP
  apply max_eq_left
  exact Valued.toNormedField.norm_le_one_iff.mpr
    ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mp hP)

theorem sourceKPArchRationalNorm (x : K) (v : InfinitePlace K) :
    ‖sourceKPArchComplexEquiv K hζ v (algebraMap K v.Completion x)‖ = v x := by
  rw [sourceKPArchComplexEquiv_norm]
  have hx : algebraMap K v.Completion x = ((WithAbs.equiv v.1).symm x : v.Completion) := by
    apply InfinitePlace.Completion.ext
    change ((algebraMap K (WithAbs v.1) x : WithAbs v.1) : v.1.Completion) =
      (((WithAbs.equiv v.1).symm x : WithAbs v.1) : v.1.Completion)
    congr 1
  rw [hx]
  simpa only [RingEquiv.apply_symm_apply] using
    (InfinitePlace.Completion.norm_coe v ((WithAbs.equiv v.1).symm x))

theorem sourceKPAdelicRationalHeight_product (x : K) :
    Height.mulHeight₁ x =
      (∏ v : InfinitePlace K,
        (max 1 ‖sourceKPArchComplexEquiv K hζ v (algebraMap K v.Completion x)‖) ^ v.mult) *
      ∏ᶠ P : HeightOneSpectrum (𝓞 K), max 1 ‖algebraMap K (P.adicCompletion K) x‖ := by
  rw [NumberField.mulHeight₁_eq]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    rw [sourceKPArchRationalNorm, max_comm]
  · rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K))]
    apply finprod_congr
    intro v
    have h := FinitePlace.norm_embedding_eq v x
    change ‖algebraMap K ((FinitePlace.equivHeightOneSpectrum v).adicCompletion K) x‖ = v x at h
    rw [h, max_comm]

theorem sourceKPAdelicHeight_decay_product (x : K) :
    (∏ v : InfinitePlace K,
      ((max 1 ‖sourceKPArchComplexEquiv K hζ v (algebraMap K v.Completion x)‖)⁻¹ ^ 2) ^ v.mult) *
      (∏ᶠ P : HeightOneSpectrum (𝓞 K), (max 1 ‖algebraMap K (P.adicCompletion K) x‖)⁻¹ ^ 2) =
        (Height.mulHeight₁ x)⁻¹ ^ 2 := by
  let A := fun v : InfinitePlace K => max 1 ‖sourceKPArchComplexEquiv K hζ v (algebraMap K v.Completion x)‖
  let F := fun P : HeightOneSpectrum (𝓞 K) => max 1 ‖algebraMap K (P.adicCompletion K) x‖
  have hF : F.HasFiniteMulSupport := sourceKPRationalFiniteMax_finite_support K x
  have ha : (∏ v : InfinitePlace K, ((A v)⁻¹ ^ 2) ^ v.mult) = (∏ v : InfinitePlace K, A v ^ v.mult)⁻¹ ^ 2 := by
    calc
      _ = ∏ v : InfinitePlace K, ((A v ^ v.mult)⁻¹) ^ 2 := by
        apply Finset.prod_congr rfl
        intro v _
        rw [pow_right_comm, inv_pow]
      _ = _ := by rw [Finset.prod_pow, Finset.prod_inv_distrib]
  have hf : (∏ᶠ P, (F P)⁻¹ ^ 2) = (∏ᶠ P, F P)⁻¹ ^ 2 := by
    calc
      _ = (∏ᶠ P, (F P)⁻¹) ^ 2 :=
        (finprod_pow (f := fun P => (F P)⁻¹) hF.inv 2).symm
      _ = _ := congrArg (fun t : ℝ => t ^ 2) (finprod_inv_distrib F)
  change (∏ v, ((A v)⁻¹ ^ 2) ^ v.mult) * (∏ᶠ P, (F P)⁻¹ ^ 2) = _
  rw [ha, hf, sourceKPAdelicRationalHeight_product K hζ x, mul_inv, mul_pow]


theorem sourceKPAdelicHeight_translate (g : GL (Fin 2) 𝔸[K]) (x : K) :
    sourceKPAdelicHeight K hζ (sourceKPAdelicOpenCellMatrix K x * g) ≤
      sourceKPAdelicHeightConstant K hζ g * (Height.mulHeight₁ x)⁻¹ ^ 2 := by
  let h := sourceKPAdelicOpenCellMatrix K x * g
  let I := fun v : InfinitePlace K => sourceArchHeight (sourceKPAdelicBaseComplexAt K hζ v h)
  let F := fun P : HeightOneSpectrum (𝓞 K) => sourceKPFiniteMatrixHeight K P (sourceKPAdelicBaseFiniteAt K P h)
  let CI := fun v : InfinitePlace K => sourceArchMatrixHeightConstant (sourceKPAdelicBaseComplexAt K hζ v g)
  let CF := fun P : HeightOneSpectrum (𝓞 K) => sourceKPFiniteMatrixHeightConstant K P (sourceKPAdelicBaseFiniteAt K P g)
  let RI := fun v : InfinitePlace K =>
    (max 1 ‖sourceKPArchComplexEquiv K hζ v (algebraMap K v.Completion x)‖)⁻¹ ^ 2
  let RF := fun P : HeightOneSpectrum (𝓞 K) =>
    (max 1 ‖algebraMap K (P.adicCompletion K) x‖)⁻¹ ^ 2
  have hIloc (v : InfinitePlace K) : I v ≤ CI v * RI v := by
    dsimp only [I, CI, RI, h]
    rw [map_mul, sourceKPAdelicOpenCellMatrix_complex]
    exact sourceArchHeight_translate _ _
  have hFloc (P : HeightOneSpectrum (𝓞 K)) : F P ≤ CF P * RF P := by
    dsimp only [F, CF, RF, h]
    rw [map_mul, sourceKPAdelicOpenCellMatrix_finite]
    exact sourceKPFiniteMatrixHeight_translate K P _ _
  have hI : (∏ v, I v ^ v.mult) ≤ (∏ v, CI v ^ v.mult) * (∏ v, RI v ^ v.mult) := by
    calc
      _ ≤ ∏ v, (CI v * RI v) ^ v.mult := by
        apply Finset.prod_le_prod₀
        · intro v _
          exact pow_nonneg (sourceArchHeight_pos _).le _
        · intro v _
          exact pow_le_pow_left₀ (sourceArchHeight_pos _).le (hIloc v) _
      _ = _ := by simp only [mul_pow, Finset.prod_mul_distrib]
  have hFs : F.HasFiniteMulSupport := sourceKPAdelicFiniteHeight_finite_support K h
  have hCFs : CF.HasFiniteMulSupport := sourceKPAdelicHeightConstant_finite_support K g
  have hRFs : RF.HasFiniteMulSupport := (sourceKPRationalFiniteMax_finite_support K x).inv.pow 2
  have hF : (∏ᶠ P, F P) ≤ (∏ᶠ P, CF P) * (∏ᶠ P, RF P) := by
    calc
      _ ≤ ∏ᶠ P, CF P * RF P := finprod_le_finprod₀ hFs
        (fun P => (sourceKPFiniteMatrixHeight_pos K P _).le) (hCFs.mul hRFs) hFloc
      _ = _ := finprod_mul_distrib hCFs hRFs
  have hF0 : 0 ≤ ∏ᶠ P, F P := by
    rw [finprod_eq_prod _ hFs]
    exact Finset.prod_nonneg (fun P _ => (sourceKPFiniteMatrixHeight_pos K P _).le)
  have hCI0 : 0 ≤ ∏ v, CI v ^ v.mult :=
    Finset.prod_nonneg (fun v _ => pow_nonneg (sourceArchMatrixHeightConstant_pos _).le _)
  have hRI0 : 0 ≤ ∏ v, RI v ^ v.mult :=
    Finset.prod_nonneg (fun v _ => pow_nonneg (sq_nonneg _) _)
  have hdecay : (∏ v, RI v ^ v.mult) * (∏ᶠ P, RF P) = (Height.mulHeight₁ x)⁻¹ ^ 2 :=
    sourceKPAdelicHeight_decay_product K hζ x
  calc
    sourceKPAdelicHeight K hζ h = (∏ v, I v ^ v.mult) * (∏ᶠ P, F P) := by
      simpa only [I, F, sourceKPFiniteMatrixHeight, sourceKPBottomMax] using sourceKPAdelicHeight_product K hζ h
    _ ≤ ((∏ v, CI v ^ v.mult) * (∏ v, RI v ^ v.mult)) *
        ((∏ᶠ P, CF P) * (∏ᶠ P, RF P)) := mul_le_mul hI hF hF0 (mul_nonneg hCI0 hRI0)
    _ = sourceKPAdelicHeightConstant K hζ g * ((∏ v, RI v ^ v.mult) * (∏ᶠ P, RF P)) := by
      change ((∏ v, CI v ^ v.mult) * (∏ v, RI v ^ v.mult)) *
        ((∏ᶠ P, CF P) * (∏ᶠ P, RF P)) =
        ((∏ v, CI v ^ v.mult) * (∏ᶠ P, CF P)) * ((∏ v, RI v ^ v.mult) * (∏ᶠ P, RF P))
      ring
    _ = _ := by rw [hdecay]

end
end ArtinMatthews
