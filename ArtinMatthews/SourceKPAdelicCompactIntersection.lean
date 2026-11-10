module

public import ArtinMatthews.SourceKPAdelicCompactSplit
public import ArtinMatthews.SourceKPAdelicUnitTorus
public import ArtinMatthews.SourceAdelicCompactBorel
public import ArtinMatthews.SourceKPAdelicMatrixLift
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

/-! Exact covering-torus coordinates of the actual compact–Borel
intersection, including the wild scalar normalization. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchComplexEquiv_norm (v : InfinitePlace K) (x : v.Completion) :
    ‖sourceKPArchComplexEquiv K hζ v x‖ = ‖x‖ := by
  have := source_isTotallyComplex K hζ
  have h := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (NumberField.IsTotallyComplex.isComplex v)).isometry.dist_eq x 0
  change dist (sourceKPArchComplexEquiv K hζ v x) (sourceKPArchComplexEquiv K hζ v 0) = dist x 0 at h
  simpa only [map_zero, dist_zero_right] using h

theorem sourceKPAdelicDeepCompact_triangular
    (g : sourceKPAdelicDeepCompactMatrix K hζ)
    (hg : ProjGenLinGroup.mk g.val ∈ sourceKPRingBorel 𝔸[K]) :
    ∃ (x : 𝔸[K]) (a : sourceKPAdelicUnitIdeles K),
      sourceKPAdelicDeepCompactLift K hζ g =
        sourceKPAdelicUpperLift K hζ x * sourceKPAdelicProjectiveDiagonalLift K hζ a.val := by
  obtain ⟨x,a,u,hfactor,_h10,h11,_h00,_h01,hf,hi⟩ :=
    sourceKPAdelicCompactBorel_factor K hζ g.val g.property.1 hg
  have hu3 : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal →
      sourceKPIdeleFiniteCoordinate K P u ∈ sourceKPUnitCubes (P.adicCompletion K) := by
    intro P h6
    obtain ⟨d,hd⟩ := g.property.2 P h6
    obtain ⟨v,hv⟩ := (sourceKPDeepLocalBase_cubeData K P d).bottom_cube
    refine ⟨v, ?_⟩
    apply Units.ext
    change ((v^3 : (P.adicCompletion K)ˣ) : P.adicCompletion K) = (u : 𝔸[K]).2 P
    rw [← hv, hd]
    exact congrArg (fun z : 𝔸[K] => z.2 P) h11
  have ha3 : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal →
      sourceKPIdeleFiniteCoordinate K P a ∈ sourceKPUnitCubes (P.adicCompletion K) := by
    intro P h6
    obtain ⟨d,hd⟩ := g.property.2 P h6
    obtain ⟨v,hv⟩ := (sourceKPDeepLocalBase_cubeData K P d).top_cube
    obtain ⟨w,hw⟩ := (sourceKPDeepLocalBase_cubeData K P d).bottom_cube
    refine ⟨v/w, ?_⟩
    apply Units.ext
    change (((v/w)^3 : (P.adicCompletion K)ˣ) : P.adicCompletion K) = (a : 𝔸[K]).2 P
    rw [div_pow, Units.val_div_eq_div_val, ← hv, ← hw, hd]
    exact (hf P).2.2.symm
  have ha : a ∈ sourceKPAdelicUnitIdeles K := by
    refine ⟨?_, ?_, ?_⟩
    · intro P
      exact (hf P).2.1
    · intro P h6
      exact ha3 P h6
    · intro v
      change ‖(a : 𝔸[K]).1 v‖ = 1
      rw [← sourceKPArchComplexEquiv_norm K hζ v]
      exact (hi v).2.1
  let b := sourceKPUpperMatrix 𝔸[K] x * sourceKPDiagonalHom 𝔸[K] a
  have hb : b ∈ sourceKPRingNormalizedBorel 𝔸[K] :=
    (sourceKPRingNormalizedBorel 𝔸[K]).mul_mem
      (sourceKPRingNormalizedBorel_upper 𝔸[K] x) (sourceKPRingNormalizedBorel_diagonal 𝔸[K] a)
  have hb00 : b 0 0 = (a : 𝔸[K]) := by
    simp [b, sourceKPUpperMatrix, sourceKPDiagonalHom, Matrix.mul_apply, Fin.sum_univ_two]
  have hbdet : (GeneralLinearGroup.det b : 𝔸[K]) = (a : 𝔸[K]) := by
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, hb00, hb.1, hb.2,
      mul_one, mul_zero, sub_zero]
  have hbval : ∀ P, sourceKPFiniteVal K P
      (GeneralLinearGroup.det (sourceKPAdelicBaseFiniteAt K P b) : P.adicCompletion K) = 1 := by
    intro P
    have hdet : (GeneralLinearGroup.det (sourceKPAdelicBaseFiniteAt K P b) : P.adicCompletion K) =
        (a : 𝔸[K]).2 P := by
      calc
        _ = (GeneralLinearGroup.det b : 𝔸[K]).2 P := by
          change Matrix.det (sourceKPAdelicBaseFiniteAt K P b : Matrix (Fin 2) (Fin 2) (P.adicCompletion K)) =
            (Matrix.det (b : Matrix (Fin 2) (Fin 2) 𝔸[K])).2 P
          rw [Matrix.det_fin_two, Matrix.det_fin_two]
          rfl
        _ = _ := congrArg (fun z : 𝔸[K] => z.2 P) hbdet
    rw [hdet]
    exact (hf P).2.1
  refine ⟨x, ⟨a,ha⟩, ?_⟩
  rw [← sourceKPAdelicMatrixLift_deepCompact, hfactor,
    sourceKPAdelicMatrixLift_normalized_scalar K hζ b hb u (fun P => (hf P).1) hbval hu3,
    sourceKPAdelicMatrixLift_upper_diagonal]

end
end ArtinMatthews
