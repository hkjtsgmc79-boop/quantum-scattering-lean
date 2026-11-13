/- F1 candidate: stable public framework endpoint. Arbitrary finite geometry,
not an abstract S-matrix assumed to be physical. Not kernel-verified yet. -/
import QuantumScattering.PhysicalModel
import QuantumScattering.StackUniqueness
import QuantumScattering.ExteriorModes
import QuantumScattering.EvolutionInterface

noncomputable section
namespace QuantumScattering

/-- Output contract, all fields are concluded from the physical input.
No solution, transfer matrix, current balance or S matrix is supplied by users. -/
structure FiniteScatteringCertificate (p : PhysicalProblem) : Prop where
  existence_uniqueness : ∀ iL iR : ℂ,
    ∃! fv : (ℝ→ℂ)×(ℝ→ℂ), p.problem.Admissible iL iR fv.1 fv.2
  regularity : ∀ iL iR : ℂ, ContDiff ℝ 1 (p.problem.wave iL iR)
  physical_equation : ∀ (iL iR : ℂ) (x : ℝ), x∉p.problem.jumps →
    -(p.hbar^2/(2*p.mass) : ℝ) • deriv (deriv (p.problem.wave iL iR)) x +
      p.potential x • p.problem.wave iL iR x=p.energy • p.problem.wave iL iR x
  actual_flux : ∀ (iL iR : ℂ) (x : ℝ),
    current p.hbar p.mass (p.problem.wave iL iR) x=
      (p.hbar/p.mass)*(absSq iL-absSq (p.problem.outgoing iL iR).1)
  unitary_left : p.problem.channels.scatteringMatrix.conjTranspose*
    p.problem.channels.scatteringMatrix=1
  unitary_right : p.problem.channels.scatteringMatrix*
    p.problem.channels.scatteringMatrix.conjTranspose=1
  reciprocal : p.problem.channels.scatteringMatrix.transpose=p.problem.channels.scatteringMatrix
  left_modes : ∀ (iL iR : ℂ) (x : ℝ), x<0 →
    p.problem.wave iL iR x=
      (iL*plane p.problem.left.k x+
        (p.problem.outgoing iL iR).1*plane (-p.problem.left.k) x)/(p.problem.left.root : ℂ)
  right_modes : ∀ (iL iR : ℂ) (x : ℝ), Stack.width p.problem.layers ≤ x →
    p.problem.wave iL iR x=
      ((p.problem.outgoing iL iR).2*plane p.problem.right.k (x-Stack.width p.problem.layers)+
        iR*plane (-p.problem.right.k) (x-Stack.width p.problem.layers))/(p.problem.right.root : ℂ)
  positive_transmission : 0<p.problem.channels.transmission
  transparent_iff : p.problem.channels.transmission=1 ↔ p.problem.channels.beta=0

/-- Constructive reusable endpoint, quantified over any finite list of layers. -/
theorem finite_piecewise_real_scattering (p : PhysicalProblem) : FiniteScatteringCertificate p where
  existence_uniqueness := p.problem.existsUnique_classical_scattering
  regularity := p.problem.C1
  physical_equation := p.schrodinger
  actual_flux := fun iL iR x => p.problem.current_left iL iR p.hbar p.mass x
  unitary_left := p.problem.channels.unitary_matrix.1
  unitary_right := p.problem.channels.unitary_matrix.2
  reciprocal := p.problem.channels.symmetric_matrix
  left_modes := p.problem.left_plane_wave
  right_modes := p.problem.right_plane_wave
  positive_transmission := p.problem.channels.transmission_positive
  transparent_iff := p.problem.channels.transparent_iff

/-- The number of layers is not a fixed constant or an external numerical bound. -/
theorem any_finite_real_layers
    (hbar mass energy vLeft vRight : ℝ) (layers : List PhysicalLayer)
    (hh : 0<hbar) (hm : 0<mass) (hl : vLeft<energy) (hr : vRight<energy) :
    FiniteScatteringCertificate
      ⟨hbar,mass,energy,vLeft,vRight,layers,hh,hm,hl,hr⟩ :=
  finite_piecewise_real_scattering _

end QuantumScattering
