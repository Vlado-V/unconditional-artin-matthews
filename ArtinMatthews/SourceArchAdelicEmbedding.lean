module

public import ArtinMatthews.SourceKPAdelicProjective
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! A genuine single-infinite-place embedding into the existing
adelic projective group. Units fill every other place with the identity. -/
namespace ArtinMatthews.SourceArchJacquet

open NumberField Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups Classical
noncomputable section

variable (F : Type) [Field F]

def sourceArchAdeleEval (v : InfinitePlace F) : InfiniteAdeleRing F →+* v.Completion where
  toFun x := x v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def sourceArchGLPiEquiv :
    GL (Fin 2) (InfiniteAdeleRing F) ≃* ∀ v : InfinitePlace F, GL (Fin 2) v.Completion :=
  (Units.mapEquiv (Matrix.piRingEquiv (n := Fin 2)
    (β := fun v : InfinitePlace F => v.Completion)).toMulEquiv).trans MulEquiv.piUnits

theorem sourceArchGLPiEquiv_apply (g : GL (Fin 2) (InfiniteAdeleRing F))
    (v : InfinitePlace F) (i j : Fin 2) :
    sourceArchGLPiEquiv F g v i j = g i j v := rfl

def sourceArchSingleGL (v : InfinitePlace F) :
    GL (Fin 2) v.Completion →* GL (Fin 2) (InfiniteAdeleRing F) :=
  (sourceArchGLPiEquiv F).symm.toMonoidHom.comp
    (MonoidHom.mulSingle (fun w : InfinitePlace F => GL (Fin 2) w.Completion) v)

def sourceArchSingleUnit (v : InfinitePlace F) :
    v.Completionˣ →* (InfiniteAdeleRing F)ˣ :=
  MulEquiv.piUnits.symm.toMonoidHom.comp
    (MonoidHom.mulSingle (fun w : InfinitePlace F => w.Completionˣ) v)

theorem sourceArchGLPiEquiv_single (v : InfinitePlace F) (g : GL (Fin 2) v.Completion) :
    sourceArchGLPiEquiv F (sourceArchSingleGL F v g) = Pi.mulSingle v g := by
  exact (sourceArchGLPiEquiv F).apply_symm_apply _

theorem sourceArchGLPiEquiv_scalar (u : (InfiniteAdeleRing F)ˣ) (v : InfinitePlace F) :
    sourceArchGLPiEquiv F (GeneralLinearGroup.scalar (Fin 2) u) v =
      GeneralLinearGroup.scalar (Fin 2) (MulEquiv.piUnits u v) := by
  apply GeneralLinearGroup.ext
  intro i j
  change (Matrix.diagonal (fun _ : Fin 2 => (u : InfiniteAdeleRing F))) i j v =
    (Matrix.diagonal (fun _ : Fin 2 => ((MulEquiv.piUnits u v : v.Completionˣ) : v.Completion))) i j
  by_cases h : i = j <;> simp [h] <;> rfl

theorem sourceArchSingleGL_scalar (v : InfinitePlace F) (u : v.Completionˣ) :
    sourceArchSingleGL F v (GeneralLinearGroup.scalar (Fin 2) u) =
      GeneralLinearGroup.scalar (Fin 2) (sourceArchSingleUnit F v u) := by
  apply (sourceArchGLPiEquiv F).injective
  rw [sourceArchGLPiEquiv_single]
  funext w
  rw [sourceArchGLPiEquiv_scalar]
  have hu : MulEquiv.piUnits (sourceArchSingleUnit F v u) = Pi.mulSingle v u :=
    MulEquiv.piUnits.apply_symm_apply _
  rw [congrFun hu w]
  by_cases hw : w = v
  · subst w
    simp
  · simp [Pi.mulSingle_eq_of_ne hw]

def sourceArchSinglePGL (v : InfinitePlace F) : PGL(2, v.Completion) →* PGL(2, InfiniteAdeleRing F) :=
  ProjGenLinGroup.lift (ProjGenLinGroup.mk.comp (sourceArchSingleGL F v)) (by
    ext u
    change ProjGenLinGroup.mk (sourceArchSingleGL F v (GeneralLinearGroup.scalar (Fin 2) u)) = 1
    rw [sourceArchSingleGL_scalar, ProjGenLinGroup.mk_scalar])

theorem sourceArchSinglePGL_mk (v : InfinitePlace F) (g : GL (Fin 2) v.Completion) :
    sourceArchSinglePGL F v (ProjGenLinGroup.mk g) = ProjGenLinGroup.mk (sourceArchSingleGL F v g) := rfl

theorem sourceArchSingleGL_place (v : InfinitePlace F) (g : GL (Fin 2) v.Completion) :
    GeneralLinearGroup.map (sourceArchAdeleEval F v)
      (sourceArchSingleGL F v g) = g := by
  apply GeneralLinearGroup.ext
  intro i j
  change (sourceArchSingleGL F v g) i j v = g i j
  have h := congrArg (fun p => p v i j) (sourceArchGLPiEquiv_single F v g)
  simpa only [sourceArchGLPiEquiv_apply, Pi.mulSingle_eq_same] using h

theorem sourceArchSinglePGL_place (v : InfinitePlace F) (g : PGL(2, v.Completion)) :
    ProjGenLinGroup.map (sourceArchAdeleEval F v)
      (sourceArchSinglePGL F v g) = g := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g =>
    rw [sourceArchSinglePGL_mk, ProjGenLinGroup.map_mk, sourceArchSingleGL_place]

theorem sourceArchSinglePGL_injective (v : InfinitePlace F) :
    Function.Injective (sourceArchSinglePGL F v) := by
  intro g h he
  simpa only [sourceArchSinglePGL_place] using congrArg
    (ProjGenLinGroup.map (sourceArchAdeleEval F v)) he

variable [NumberField F]

def sourceArchLocalToAdelic {ζ : F} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace F) :
    PGL(2, v.Completion) →* SourceKPAdelicProjective F hζ :=
  (sourceArchSinglePGL F v).prod (1 : PGL(2, v.Completion) →* SourceKPFiniteAdeleProjective F hζ)

theorem sourceArchLocalToAdelic_apply {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
    (v : InfinitePlace F) (g : PGL(2, v.Completion)) :
    sourceArchLocalToAdelic F hζ v g = (sourceArchSinglePGL F v g, 1) := rfl

theorem sourceArchLocalToAdelic_injective {ζ : F} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace F) :
    Function.Injective (sourceArchLocalToAdelic F hζ v) := by
  intro g h he
  exact sourceArchSinglePGL_injective F v (congrArg Prod.fst he)

end
end ArtinMatthews.SourceArchJacquet
