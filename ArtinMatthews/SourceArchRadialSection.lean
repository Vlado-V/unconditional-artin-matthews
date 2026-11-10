module

public import ArtinMatthews.SourceKPArchRadialFlow
public import ArtinMatthews.SourceArchGramNormalForm
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

/-! The literal upper section follows the same all-place radial flow. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

theorem sourceArchRadialFlow_section_scalar (t : ℝ) (p : SourceArchUpperHalfSpace) :
    ∃ u : ℂˣ, sourceArchRadialFlow t (sourceArchUpperHalfSection p) =
      sourceArchUpperHalfSection (sourceArchRadialPoint t p) * GeneralLinearGroup.scalar (Fin 2) u := by
  let r : ℂˣ := Units.mk0 (Real.sqrt p.2.val : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr p.2.property).ne')
  let r' : ℂˣ := Units.mk0 (Real.sqrt (Real.exp t*p.2.val) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos (Real.exp_pos t) p.2.property)).ne')
  let y : ℂˣ := Units.mk0 (p.2.val : ℂ) (Complex.ofReal_ne_zero.mpr p.2.property.ne')
  let y' : ℂˣ := Units.mk0 ((Real.exp t*p.2.val : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (mul_pos (Real.exp_pos t) p.2.property).ne')
  have hs : sourceArchUpperHalfSection p * scalar (Fin 2) r =
      sourceGL2Upper p.1 * sourceGL2Diagonal y :=
    sourceArchUpperSection_scalar p.1 p.2.val p.2.property
  have hs' : sourceArchUpperHalfSection (sourceArchRadialPoint t p) * scalar (Fin 2) r' =
      sourceGL2Upper p.1 * sourceGL2Diagonal y' :=
    sourceArchUpperSection_scalar p.1 (Real.exp t*p.2.val) (mul_pos (Real.exp_pos t) p.2.property)
  have hb : sourceGL2Upper p.1 * sourceGL2Diagonal y ∈ sourceGL2NormalizedBorel ℂ := by
    constructor <;> simp [sourceGL2Upper, sourceGL2Diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  have hz : sourceArchGramShift (sourceGL2Upper p.1 * sourceGL2Diagonal y) = p.1 := by
    have h := congrArg Prod.fst (sourceArchGramCoordinates_borel _ hb)
    simpa [sourceArchGramCoordinates, sourceGL2Upper, sourceGL2Diagonal,
      Matrix.mul_apply, Fin.sum_univ_two] using h
  have hflow : sourceArchRadialFlow t (sourceGL2Upper p.1 * sourceGL2Diagonal y) =
      sourceGL2Upper p.1 * sourceGL2Diagonal y' := by
    rw [sourceArchRadialFlow, hz]
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceArchRadialBorel_entry, sourceGL2Upper, sourceGL2Diagonal,
        Matrix.mul_apply, Fin.sum_univ_two, y, y', Complex.ofReal_mul]
    ring
  refine ⟨r'*r⁻¹, ?_⟩
  have h : sourceArchRadialFlow t (sourceArchUpperHalfSection p) * scalar (Fin 2) r =
      sourceArchUpperHalfSection (sourceArchRadialPoint t p) * scalar (Fin 2) r' := by
    rw [← sourceArchRadialFlow_scalar, hs, hflow, hs']
  apply mul_right_cancel (b := scalar (Fin 2) r)
  rw [h, map_mul, map_inv]
  group

theorem sourceArchRadialFlow_section_projective (t : ℝ) (p : SourceArchUpperHalfSpace) :
    ProjGenLinGroup.mk (sourceArchRadialFlow t (sourceArchUpperHalfSection p)) =
      ProjGenLinGroup.mk (sourceArchUpperHalfSection (sourceArchRadialPoint t p)) := by
  obtain ⟨u,hu⟩ := sourceArchRadialFlow_section_scalar t p
  rw [hu, map_mul, ProjGenLinGroup.mk_scalar, mul_one]

end
end ArtinMatthews.SourceArchJacquet

namespace ArtinMatthews
open NumberField Matrix SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchRadialFlow_section (t : ℝ) (p : SourceKPArchUpperHalfSpace K) :
    sourceKPArchRadialFlow K hζ t (ProjGenLinGroup.mk (sourceKPArchUpperHalfSection K hζ p)) =
      ProjGenLinGroup.mk (sourceKPArchUpperHalfSection K hζ (sourceKPArchRadialPoint K t p)) := by
  choose u hu using fun v : InfinitePlace K => sourceArchRadialFlow_section_scalar t (p v)
  let d : (InfiniteAdeleRing K)ˣ := MulEquiv.piUnits.symm
    (fun v => Units.map (sourceKPArchComplexEquiv K hζ v).symm (u v))
  have hd (v : InfinitePlace K) :
      Units.map (sourceKPArchComplexEquiv K hζ v) (MulEquiv.piUnits d v) = u v := by
    dsimp only [d]
    rw [MulEquiv.apply_symm_apply]
    apply Units.ext
    exact (sourceKPArchComplexEquiv K hζ v).apply_symm_apply _
  have hg : sourceKPArchRadialFlowMatrix K hζ t (sourceKPArchUpperHalfSection K hζ p) =
      sourceKPArchUpperHalfSection K hζ (sourceKPArchRadialPoint K t p) *
        GeneralLinearGroup.scalar (Fin 2) d := by
    apply (sourceArchGLPiEquiv K).injective
    funext v
    apply (sourceKPArchMatrixComplexEquiv K hζ v).injective
    simp only [sourceKPArchRadialFlowMatrix_at, sourceKPArchUpperHalfSection_at,
      map_mul, Pi.mul_apply, sourceArchGLPiEquiv_scalar, sourceKPArchMatrixComplexEquiv_scalar, hd]
    exact hu v
  rw [sourceKPArchRadialFlow_mk, hg, map_mul, ProjGenLinGroup.mk_scalar, mul_one]

end
end ArtinMatthews
