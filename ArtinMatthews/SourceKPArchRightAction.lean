module

public import ArtinMatthews.SourceKPArchCompactOrbifold
public import ArtinMatthews.GroupDoubleQuotient
public import ArtinMatthews.SourceKPFiniteOrbit
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

/-! The right archimedean action on the actual finite level and rational
quotient. -/
namespace ArtinMatthews
open NumberField Matrix Topology MulOpposite
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPFiniteLevel_archRightAction :
    MulAction (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ (SourceKPFiniteLevelSpace K hζ) where
  smul h x := (x.1 * unop h, x.2)
  one_smul x := Prod.ext (mul_one x.1) rfl
  mul_smul h k x := Prod.ext (mul_assoc x.1 (unop k) (unop h)).symm rfl

@[simp] theorem sourceKPFiniteLevel_archRight_smul
    (h : (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ) (x : SourceKPFiniteLevelSpace K hζ) :
    h • x = (x.1 * unop h,x.2) := rfl

instance sourceKPFiniteLevel_archRight_continuous :
    ContinuousSMul (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ (SourceKPFiniteLevelSpace K hζ) where
  continuous_smul := by
    change Continuous (fun p : (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ ×
      SourceKPFiniteLevelSpace K hζ => (p.2.1 * unop p.1,p.2.2))
    exact (((continuous_fst.comp continuous_snd).mul
      (continuous_unop.comp continuous_fst))).prodMk (continuous_snd.comp continuous_snd)

instance sourceKPFiniteLevel_archRight_comm :
    SMulCommClass (PGL(2, K)) (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ
      (SourceKPFiniteLevelSpace K hζ) where
  smul_comm γ h x := Prod.ext (mul_assoc (sourceKPRationalArchMap K hζ γ) x.1 (unop h)).symm rfl

instance sourceKPFiniteLevel_rational_continuousConst :
    ContinuousConstSMul (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ) :=
  ⟨sourceKPFiniteLevel_rational_continuous K hζ⟩

instance sourceKPRationalQuotient_archRightAction :
    MulAction (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ
      (Quotient (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ))) :=
  sourceCommutingOrbitAction (PGL(2, K)) (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ
    (SourceKPFiniteLevelSpace K hζ)

instance sourceKPAutomorphicLevel_archRightAction :
    MulAction (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ (SourceKPAutomorphicLevel K hζ) :=
  inferInstanceAs (MulAction (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ
    (Quotient (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ))))

@[simp] theorem sourceKPAutomorphicLevel_archRight_mk
    (h : (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ) (x : SourceKPFiniteLevelSpace K hζ) :
    h • (Quotient.mk _ x : SourceKPAutomorphicLevel K hζ) = Quotient.mk _ (h • x) := rfl

@[simp] theorem sourceKPAutomorphicLevelMk_archRight
    (h : (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ) (g : SourceKPAdelicProjective K hζ) :
    h • sourceKPAutomorphicLevelMk K hζ g =
      sourceKPAutomorphicLevelMk K hζ (g.1 * unop h,g.2) := rfl

instance sourceKPRationalQuotient_archRight_continuous :
    ContinuousSMul (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ
      (Quotient (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ))) :=
  sourceCommutingOrbitAction_continuous (PGL(2, K)) (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ
    (SourceKPFiniteLevelSpace K hζ)

instance sourceKPAutomorphicLevel_archRight_continuous :
    ContinuousSMul (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ (SourceKPAutomorphicLevel K hζ) :=
  inferInstanceAs (ContinuousSMul (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ
    (Quotient (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ))))

@[simp] theorem sourceKPArchComponentPoint_archRight (b : SourceKPFiniteLevelFiber K hζ)
    (h : (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ) (a : PGL(2, InfiniteAdeleRing K)) :
    h • sourceKPArchComponentPoint K hζ b a =
      sourceKPArchComponentPoint K hζ b (a * unop h) := rfl

theorem sourceKPArchComponentEmbedding_archRight (b : SourceKPFiniteLevelFiber K hζ)
    (h : (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ)
    (x : Quotient (QuotientGroup.rightRel (sourceKPArchComponentSubgroup K hζ b))) :
    sourceKPArchComponentEmbedding K hζ b (h • x) =
      h • sourceKPArchComponentEmbedding K hζ b x := by
  induction x using Quotient.inductionOn with
  | _ x => rfl

@[simp] theorem sourceKPAutomorphicFiniteOrbit_archRight
    (h : (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ) (x : SourceKPAutomorphicLevel K hζ) :
    sourceKPAutomorphicFiniteOrbit K hζ (h • x) = sourceKPAutomorphicFiniteOrbit K hζ x := by
  induction x using Quotient.inductionOn with
  | _ x => rfl

abbrev SourceKPArchCompactRightGroup := (sourceKPArchBaseCompactSubgroup K hζ).op

instance sourceKPArchCompactRightGroup_compact : CompactSpace (SourceKPArchCompactRightGroup K hζ) := by
  apply isCompact_iff_compactSpace.mp
  exact (opHomeomorph.isCompact_preimage).mp (sourceKPArchBaseCompactSubgroup_isCompact K hζ)

instance sourceKPFiniteLevel_compactRight_continuous :
    ContinuousSMul (SourceKPArchCompactRightGroup K hζ) (SourceKPFiniteLevelSpace K hζ) :=
  inferInstance

instance sourceKPAutomorphicLevel_compactRight_continuous :
    ContinuousSMul (SourceKPArchCompactRightGroup K hζ) (SourceKPAutomorphicLevel K hζ) :=
  inferInstance

end
end ArtinMatthews
