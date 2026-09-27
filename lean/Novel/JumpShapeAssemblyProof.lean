import Standalone.JumpShapeAssembly
import Novel.JumpShapeTwoPointProof
import Novel.JumpShapeLaterProof
import Novel.JumpShapeOriginProof
import Novel.JumpShapeGeneralProof
import Novel.JumpShapeExistProof

namespace Novel.JumpShapeAssemblyProof

theorem jumpShapeAssembly : Standalone.JumpShapeAssembly.statement :=
  ⟨Novel.JumpShapeKernelProof.jumpShapeKernel, Novel.JumpShapeProfileProof.jumpShapeProfile,
    Novel.JumpShapeAffineProof.jumpShapeAffine, Novel.JumpShapeCondProof.jumpShapeCond,
    Novel.JumpShapeCondBProof.jumpShapeCondB, Novel.JumpShapeOriginProof.jumpShapeOrigin,
    Novel.JumpShapeExistProof.jumpShapeExist, Novel.JumpShapeTwoPointProof.jumpShapeTwoPoint,
    Novel.JumpShapeForwardProof.jumpShapeForward, Novel.JumpShapeGeneralProof.jumpShapeGeneral,
    Novel.JumpShapeLaterProof.jumpShapeLater⟩

end Novel.JumpShapeAssemblyProof
