module

public import ArtinMatthews.MarkedPhysicalRootCoordinates
public import ArtinMatthews.MarkedRootProjectiveRootLift
public import ArtinMatthews.FixedURootWeightedGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! The actual integer root matrix and its projective residue tests.
Primitivity and every prescribed matrix entry survive the coordinate lift. -/

noncomputable section
namespace ArtinMatthews
open scoped LinearAlgebra.Projectivization

def markedPhysicalRootMatrix (root completion : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion = 1) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![root.1,completion.1;root.2,completion.2], by
    simpa [Matrix.det_fin_two, markedMinorIntegerDet, mul_comm] using hdet⟩

theorem markedPhysicalRootLift_primitive_iff (root completion z : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion = 1) :
    IsCoprime (markedPhysicalRootLift root completion z).1
      (markedPhysicalRootLift root completion z).2 ↔ IsCoprime z.1 z.2 := by
  constructor
  · rintro ⟨a,b,hab⟩
    refine ⟨a*root.1+b*root.2,a*completion.1+b*completion.2,?_⟩
    change a*(z.1*root.1+z.2*completion.1)+b*(z.1*root.2+z.2*completion.2)=1 at hab
    linear_combination hab
  · rintro ⟨a,b,hab⟩
    refine ⟨a*completion.2-b*root.2,-a*completion.1+b*root.1,?_⟩
    change (a*completion.2-b*root.2)*(z.1*root.1+z.2*completion.1)+
      (-a*completion.1+b*root.1)*(z.1*root.2+z.2*completion.2)=1
    calc
      _ = markedMinorIntegerDet root completion*(a*z.1+b*z.2) := by
        unfold markedMinorIntegerDet
        ring
      _ = 1 := by rw [hdet,hab,one_mul]

theorem markedPhysicalRootCoordinates_primitive_iff (root completion target : ℤ × ℤ)
    (hdet : markedMinorIntegerDet root completion = 1) :
    IsCoprime (markedPhysicalRootCoordinates root completion target).1
      (markedPhysicalRootCoordinates root completion target).2 ↔ IsCoprime target.1 target.2 := by
  have h := markedPhysicalRootLift_primitive_iff root completion
    (markedPhysicalRootCoordinates root completion target) hdet
  rw [markedPhysicalRootLift_coordinates root completion target hdet] at h
  exact h.symm

theorem markedPhysicalRootMatrix_reduction {S : ℕ}
    (root completion : ℤ × ℤ) (hdet : markedMinorIntegerDet root completion = 1)
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (hentries : (!![(root.1 : ZMod S),(completion.1 : ZMod S);
      (root.2 : ZMod S),(completion.2 : ZMod S)] : Matrix (Fin 2) (Fin 2) (ZMod S)) = g₀) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S))
      (markedPhysicalRootMatrix root completion hdet) = g₀ := by
  apply Subtype.ext
  change (Int.castRingHom (ZMod S)).mapMatrix
      !![root.1,completion.1;root.2,completion.2] = (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S))
  have hm : (Int.castRingHom (ZMod S)).mapMatrix
      !![root.1,completion.1;root.2,completion.2] =
      !![(root.1 : ZMod S),(completion.1 : ZMod S);(root.2 : ZMod S),(completion.2 : ZMod S)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  exact hm.trans hentries

/-- Prime hits of the actual lifted target are exactly the literal finite
kernel-line tests in the prescribed root residue. -/
theorem markedPhysicalRootLift_kernel_hit {S : ℕ} (hS : Squarefree S)
    (root completion : ℤ × ℤ) (hdet : markedMinorIntegerDet root completion = 1)
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (hred : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S))
      (markedPhysicalRootMatrix root completion hdet) = g₀)
    (p : S.primeFactors) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) :
    ((p : ℕ) : ℤ) ∣ (markedPhysicalRootLift root completion z).1 ↔
      markedPrimePositionLine (p : ℕ) z hz = markedRootKernelTuple hS g₀ p := by
  have h := markedRootKernelTuple_prime_hit_iff hS
    (markedPhysicalRootMatrix root completion hdet) p z hz
  rw [hred] at h
  convert h using 2
  change z.1*root.1+z.2*completion.1 = root.1*z.1+completion.1*z.2
  ring

/-- Every counted canonical root supplies its actual integral determinant-one
matrix reducing to the prescribed class. -/
theorem fixedURootMatrixBox_integer_root {S : ℕ} [NeZero S]
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (A B α β C D : ℝ) (lcR rcR : Bool) (hA : 1 < A) (hC : 1 < C)
    (hα : 0 ≤ α) (hβ : β ≤ 1) (p : Σ _u : ℤ, ℤ × ℤ)
    (hp : p ∈ fixedURootMatrixBoxPoints g₀ A B α β C D true true lcR rcR true true) :
    ∃ d : ℤ, ∃ hdet : markedMinorIntegerDet (p.1,p.2.2) (p.2.1,d) = 1,
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S))
        (markedPhysicalRootMatrix (p.1,p.2.2) (p.2.1,d) hdet) = g₀ := by
  rcases p with ⟨u,c,v⟩
  obtain ⟨d,_,_,_,_,_,_,hd,hdr⟩ := fixedURootReciprocal_box_canonical hA hC hα hβ hp
  have hdet : markedMinorIntegerDet (u,v) (c,d) = 1 := hd
  refine ⟨d,hdet,?_⟩
  apply markedPhysicalRootMatrix_reduction
  have hs := Finset.mem_sigma.mp hp
  have hur := (Finset.mem_filter.mp hs.1).2
  have hpairs := (Finset.mem_filter.mp hs.2).2
  exact (fixedURootMatrix_modEq_iff g₀ u c v d).mpr ⟨hur,hpairs.1,hpairs.2.1,hdr⟩

end ArtinMatthews
