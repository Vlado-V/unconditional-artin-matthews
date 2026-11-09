module

public import ArtinMatthews.SourceKPRetainedSeedVector
public import ArtinMatthews.SourceKPLocalRestBase


set_option backward.privateInPublic true
@[expose] public section

/-! The finite diagonal and upper lifts used in the positive seed have
actual identity projective component outside the retained places. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ

def sourceKPRetainedFiniteBase (P : Pr) : Gf →* PGL(2, P.adicCompletion K) :=
  (sourceKPAdelicLocalBase K hζ P).comp (MonoidHom.inr (PGL(2, InfiniteAdeleRing K)) Gf)

local notation "B" => sourceKPRetainedFiniteBase K hζ
def sourceKPRetainedUnitAt (P : Pr) : 𝔸ᶠ[K]ˣ →* (P.adicCompletion K)ˣ :=
  Units.map (sourceKPAdeleEval K P).toMonoidHom

local notation "unitAt" => sourceKPRetainedUnitAt K

theorem sourceKPRetainedFiniteBase_diagonal (P : Pr) (a : 𝔸ᶠ[K]ˣ) :
    B P (D a) = sourceKPProjectiveDiagonalHom (P.adicCompletion K) (unitAt P a) := by
  change ProjGenLinGroup.map (sourceKPAdeleEval K P)
    (sourceKPFiniteAdeleProjectiveProjection K hζ (D a)) = _
  rw [sourceKPFiniteAdeleProjectiveDiagonalLift_projection, sourceKPProjectiveDiagonalHom_map]
  rfl

theorem sourceKPRetainedFiniteBase_upper (P : Pr) (x : 𝔸ᶠ[K]) :
    B P (Nf x) = ProjGenLinGroup.mk (sourceGL2Upper (x P)) := by
  have hpair : sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K x) =
      ((1,Nf x) : SourceKPAdelicProjective K hζ) :=
    Prod.ext (sourceKPAdelicUpperLift_finite_fst K hζ x) rfl
  change sourceKPAdelicLocalBase K hζ P (1,Nf x) = _
  rw [← hpair]
  exact sourceKPAdelicLocalBase_upper K hζ P (sourceKPFiniteAddEmbedding K x)

theorem sourceKPRetainedDiagonalUnit_unitAt_mem
    (S : Finset Pr) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) (P : S) :
    unitAt P.val (sourceKPRetainedDiagonalUnit K S z) = z P :=
  Units.ext (sourceKPRetainedDiagonalUnit_at K S z P)

theorem sourceKPRetainedDiagonalUnit_unitAt_notMem
    (S : Finset Pr) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) (P : Pr) (hP : P ∉ S) :
    unitAt P (sourceKPRetainedDiagonalUnit K S z) = 1 := by
  rw [sourceKPRetainedDiagonalUnit, map_prod]
  apply Finset.prod_eq_one
  intro Q _
  exact sourceKPAdeleLocalUnit_other K Q.val (z Q) P (fun h => hP (h ▸ Q.prop))

theorem sourceKPRetainedFiniteBase_diagonalUnit_notMem
    (S : Finset Pr) (z : ∀ P : S, (P.val.adicCompletion K)ˣ) (P : Pr) (hP : P ∉ S) :
    B P (D (sourceKPRetainedDiagonalUnit K S z)) = 1 := by
  rw [sourceKPRetainedFiniteBase_diagonal, sourceKPRetainedDiagonalUnit_unitAt_notMem K S z P hP, map_one]

theorem sourceKPRetainedUpperSum_apply_notMem (S : Finset Pr)
    (u : ∀ P : S, P.val.adicCompletion K) (P : Pr) (hP : P ∉ S) :
    (∑ Q : S, sourceKPFiniteAdditiveSingle K Q.val (u Q)) P = 0 := by
  change sourceKPAdeleEval K P (∑ Q : S, sourceKPFiniteAdditiveSingle K Q.val (u Q)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro Q _
  exact sourceKPFiniteAdditiveSingle_other K Q.val (u Q) P (fun h => hP (h ▸ Q.prop))

theorem sourceKPRetainedFiniteBase_seedTranslate_notMem (S : Finset Pr)
    (R M : S → ℕ) (qf : Gf) (a : SourceKPRetainedSeedIndex K S R M)
    (P : Pr) (hP : P ∉ S) (hq : B P qf = 1) :
    B P (sourceKPRetainedSeedTranslate K hζ S R M qf a) = 1 := by
  rw [sourceKPRetainedSeedTranslate, map_mul, sourceKPRetainedFiniteBase_upper,
    sourceKPRetainedUpperSum_apply_notMem K S _ P hP, sourceGL2Upper_zero, map_one, hq, mul_one]

end
end ArtinMatthews
