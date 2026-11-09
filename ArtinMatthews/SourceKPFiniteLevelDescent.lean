module

public import ArtinMatthews.SourceKPFiniteLevel


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPFiniteLevelDescend {V : Type*} (f : SourceKPAdelicProjective K hζ → V)
    (hf : ∀ g k, f (g * sourceKPFiniteDeepCoverLift K hζ k) = f g) :
    SourceKPFiniteLevelSpace K hζ → V := fun x =>
  Quotient.liftOn x.2 (fun b => f (x.1,b)) (by
    intro b c hbc
    obtain ⟨k,hk⟩ := QuotientGroup.leftRel_apply.mp hbc
    calc
      f (x.1,b) = f ((x.1,b) * sourceKPFiniteDeepCoverLift K hζ k) := (hf _ k).symm
      _ = f (x.1,c) := by
        apply congrArg f
        apply Prod.ext
        · change x.1 * (sourceKPFiniteDeepCoverLift K hζ k).1 = x.1
          rw [sourceKPFiniteDeepCoverLift_fst, mul_one]
        · change b * sourceKPFiniteLevelLift K hζ k = c
          rw [hk, mul_inv_cancel_left])

theorem sourceKPFiniteLevelDescend_mk {V : Type*} (f : SourceKPAdelicProjective K hζ → V)
    (hf : ∀ g k, f (g * sourceKPFiniteDeepCoverLift K hζ k) = f g)
    (g : SourceKPAdelicProjective K hζ) :
    sourceKPFiniteLevelDescend K hζ f hf (sourceKPFiniteLevelMk K hζ g) = f g := rfl

instance : MulAction (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ) :=
  MulAction.compHom _ (sourceKPAdelicProjectiveRationalLift K hζ)

theorem sourceKPFiniteLevelMk_rational (γ : PGL(2, K)) (g : SourceKPAdelicProjective K hζ) :
    sourceKPFiniteLevelMk K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ * g) =
      γ • sourceKPFiniteLevelMk K hζ g := rfl

def SourceKPAutomorphicLevel :=
  Quotient (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ))

def sourceKPAutomorphicLevelMk (g : SourceKPAdelicProjective K hζ) : SourceKPAutomorphicLevel K hζ :=
  Quotient.mk _ (sourceKPFiniteLevelMk K hζ g)

theorem sourceKPAutomorphicLevelMk_surjective : Function.Surjective (sourceKPAutomorphicLevelMk K hζ) := by
  intro x
  induction x using Quotient.inductionOn with
  | _ x =>
    obtain ⟨g,rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ x
    exact ⟨g,rfl⟩

theorem sourceKPAutomorphicLevelMk_eq_iff (g h : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicLevelMk K hζ g = sourceKPAutomorphicLevelMk K hζ h ↔
      ∃ (γ : PGL(2, K)) (k : sourceKPFiniteDeepMatrixGroup K),
        sourceKPAdelicProjectiveRationalLift K hζ γ * h * sourceKPFiniteDeepCoverLift K hζ k = g := by
  constructor
  · intro he
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact he)
    have hh : sourceKPFiniteLevelMk K hζ (sourceKPAdelicProjectiveRationalLift K hζ γ * h) =
        sourceKPFiniteLevelMk K hζ g := hγ
    obtain ⟨k,hk⟩ := (sourceKPFiniteLevelMk_eq_iff K hζ _ _).mp hh
    exact ⟨γ,k,hk⟩
  · rintro ⟨γ,k,hk⟩
    apply Quotient.sound
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨γ,?_⟩
    exact (sourceKPFiniteLevelMk_eq_iff K hζ _ _).mpr ⟨k,hk⟩

def sourceKPAutomorphicLevelDescend {V : Type*} (f : SourceKPAdelicProjective K hζ → V)
    (hf : ∀ g k, f (g * sourceKPFiniteDeepCoverLift K hζ k) = f g)
    (hr : ∀ γ g, f (sourceKPAdelicProjectiveRationalLift K hζ γ * g) = f g) :
    SourceKPAutomorphicLevel K hζ → V :=
  Quotient.lift (sourceKPFiniteLevelDescend K hζ f hf) (by
    intro x y hxy
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp hxy
    obtain ⟨g,rfl⟩ := sourceKPFiniteLevelMk_surjective K hζ y
    rw [← hγ]
    change f (sourceKPAdelicProjectiveRationalLift K hζ γ * g) = f g
    exact hr γ g)

theorem sourceKPAutomorphicLevelDescend_mk {V : Type*} (f : SourceKPAdelicProjective K hζ → V)
    (hf : ∀ g k, f (g * sourceKPFiniteDeepCoverLift K hζ k) = f g)
    (hr : ∀ γ g, f (sourceKPAdelicProjectiveRationalLift K hζ γ * g) = f g)
    (g : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicLevelDescend K hζ f hf hr (sourceKPAutomorphicLevelMk K hζ g) = f g := rfl

end
end ArtinMatthews
