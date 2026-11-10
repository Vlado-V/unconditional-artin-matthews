module

public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceKPRadialHighFlow
public import ArtinMatthews.SourceEisensteinArchNonconstantGrowth
public import ArtinMatthews.SourceEisensteinNonconstantInvariance
public import ArtinMatthews.SourceKPAdelicBaseCompactTopology
public import ArtinMatthews.SourceKPCompactHeight
public import ArtinMatthews.SourceKPCuspBalancedDiagonal
public import ArtinMatthews.SourceKPHeightLocalContinuity
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
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual balanced radial growth of the nonconstant Eisenstein remainder
from any compact matrix set of genuine representatives. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix MulOpposite
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicNonconstantEisenstein_balanced_radial_growth {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ S, ∀ q : SourceKPAdelicProjective K hζ,
      sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g →
      ∀ t : ℝ, 0 ≤ t →
        ‖sourceKPAdelicNonconstantEisenstein K hζ s (sourceKPArchRadialFlow K hζ t q.1,q.2)‖ ≤
          C * sourceKPRadialHeightScale K t ^ (s.re+1/2) := by
  let A (g : GL (Fin 2) 𝔸[K]) := (sourceKPGL2ProductEquiv K g).1
  let B (g : GL (Fin 2) 𝔸[K]) := (sourceKPGL2ProductEquiv K g).2
  let P (g : GL (Fin 2) 𝔸[K]) := sourceKPArchGramCoordinatesMatrix K hζ (A g)
  let L (g : GL (Fin 2) 𝔸[K]) := sourceKPArchUpperHalfSection K hζ (P g)
  let G (g : GL (Fin 2) 𝔸[K]) := (sourceKPGL2ProductEquiv K).symm (L g,B g)
  have hA : Continuous A := by
    change Continuous (GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) 𝔸ᶠ[K]))
    exact continuous_fst.generalLinearGroup_map
  have hB : Continuous B := sourceKPAdelicFiniteMatrix_continuous K
  have hL : Continuous L := (sourceKPArchUpperHalfSection_continuous K hζ).comp
    ((sourceKPArchGramCoordinatesMatrix_continuous K hζ).comp hA)
  have hG : Continuous G := (sourceKPGL2ProductEquiv_symm_continuous K).comp (hL.prodMk hB)
  obtain ⟨C,hC,hbound⟩ := sourceKPAdelicNonconstantEisenstein_archDiagonal_growth K hζ hs
    (G '' S) (hS.image hG)
  refine ⟨C,hC,?_⟩
  intro g hg q hq t ht
  have hpair := congrArg (sourceKPAdelicProjectiveProductEquiv K) hq
  rw [sourceKPAdelicProjectiveProjection_product,sourceKPAdelicProjectiveProductEquiv_mk] at hpair
  change (q.1,sourceKPFiniteAdeleProjectiveProjection K hζ q.2) =
    (ProjGenLinGroup.mk (A g),ProjGenLinGroup.mk (B g)) at hpair
  have hqa := congrArg Prod.fst hpair
  have hqf := congrArg Prod.snd hpair
  let k := (ProjGenLinGroup.mk (L g))⁻¹ * q.1
  have hk : k ∈ sourceKPArchBaseCompactSubgroup K hζ := by
    apply (sourceKPArchGramCoordinates_eq_iff K hζ (ProjGenLinGroup.mk (L g)) q.1).mp
    change q.1 = ProjGenLinGroup.mk (A g) at hqa
    rw [hqa,sourceKPArchGramCoordinates_mk,sourceKPArchGramCoordinates_mk]
    exact sourceKPArchGramCoordinatesMatrix_section K hζ (P g)
  have hkD : (k,1) ∈ sourceKPAdelicDeepCompact K hζ :=
    sourceKPArchCompactRight_deep K hζ ⟨op k,hk⟩
  have hqk : q.1 = ProjGenLinGroup.mk (L g) * k := by
    dsimp only [k]
    group
  let q₀ : SourceKPAdelicProjective K hζ :=
    (sourceKPArchRadialFlow K hζ t (ProjGenLinGroup.mk (L g)),q.2)
  have hq₀ : (sourceKPArchRadialFlow K hζ t q.1,q.2) = q₀ * (k,1) := by
    apply Prod.ext
    · change sourceKPArchRadialFlow K hζ t q.1 =
        sourceKPArchRadialFlow K hζ t (ProjGenLinGroup.mk (L g))*k
      rw [hqk,sourceKPArchRadialFlow_compact K hζ t _ k hk]
    · exact (mul_one q.2).symm
  have hright := sourceKPAdelicNonconstantEisenstein_deepCompact_right K hζ s q₀ ⟨(k,1),hkD⟩
  change sourceKPAdelicNonconstantEisenstein K hζ s (q₀*(k,1)) = _ at hright
  rw [hq₀,hright]
  let a := sourceKPBalancedArchUnit K hζ t
  have ha (v : InfinitePlace K) : 1 ≤ ‖(a : InfiniteAdeleRing K) v‖ := by
    change 1 ≤ ‖(sourceKPBalancedArchUnit K hζ t : InfiniteAdeleRing K) v‖
    rw [sourceKPBalancedArchUnit_norm_at]
    exact Real.one_le_exp_iff.mpr ht
  have hp : sourceKPAdelicProjectiveProjection K hζ q₀ =
      ProjGenLinGroup.mk (G g * sourceKPDiagonalHom 𝔸[K] (sourceArchOnlyIdele K a)) := by
    apply (sourceKPAdelicProjectiveProductEquiv K).injective
    rw [sourceKPAdelicProjectiveProjection_product,sourceKPAdelicProjectiveProductEquiv_mk,map_mul,
      sourceKPArchOnlyDiagonal_product]
    have he : sourceKPGL2ProductEquiv K (G g) = (L g,B g) := MulEquiv.apply_symm_apply _ _
    rw [he]
    change (sourceKPArchRadialFlow K hζ t (ProjGenLinGroup.mk (L g)),
      sourceKPFiniteAdeleProjectiveProjection K hζ q.2) =
        (ProjGenLinGroup.mk (L g * sourceKPDiagonalHom (InfiniteAdeleRing K) a),
          ProjGenLinGroup.mk (B g*1))
    change sourceKPFiniteAdeleProjectiveProjection K hζ q.2 = ProjGenLinGroup.mk (B g) at hqf
    rw [hqf,mul_one,sourceKPArchRadialFlow_mk]
    exact congrArg (fun m => (ProjGenLinGroup.mk m,ProjGenLinGroup.mk (B g)))
      (sourceKPArchRadialFlowMatrix_section_diagonal K hζ t (P g))
  have hh := hbound (G g) ⟨g,hg,rfl⟩ a ha q₀ hp
  change _ ≤ C * ‖(sourceKPBalancedArchUnit K hζ t : InfiniteAdeleRing K)‖ ^ (s.re+1/2) at hh
  rw [sourceKPBalancedArchUnit_norm] at hh
  exact hh

end
end ArtinMatthews
