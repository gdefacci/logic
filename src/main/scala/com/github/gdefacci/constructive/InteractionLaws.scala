package com.github.gdefacci.constructive

object InteractionLaws {

  def l1[A <: Expr, B <: Expr, C <: Expr]: (A And (B And C)) Eq ((A And B) And C) = Eq(
    h => And(And(h.left, h.right.left), h.right.right),
    h => And(h.left.left, And(h.left.right, h.right)))

  def l2[A <: Expr]: (A And True.type) Eq A = Eq(
    h => h.left,
    h => And(h, True))

  def l4[A <: Expr, B <: Expr, C <: Expr]: (A And (B Or C)) Eq ((A And B) Or (A And C)) = Eq(
    { h =>
      val a = h.left
      h.right.orElimination[(A And B) Or (A And C)](
        (b: B) => Or.left(And(a, b)),
        (c: C) => Or.right(And(a, c)))
    },
    { h =>
      h.orElimination[A And (B Or C)](
        { h: (A And B) => And(h.left, Or.left(h.right)) },
        { h: (A And C) => And(h.left, Or.right(h.right)) })
    })

  def l5[A <: Expr]: (A And Bottom) Eq Bottom = Eq(
    h => h.right,
    h => Bottom.elimination(h))

  def l6[A <: Expr, B <: Expr, C <: Expr]: (A Or (B And C)) Eq ((A Or B) And (A Or C)) = Eq(
    { h =>
      val aOrB = h.orElimination[A Or B](
        a => Or.left(a),
        bAndC => Or.right(bAndC.left))

      val aOrC = h.orElimination[A Or C](
        a => Or.left(a),
        bAndC => Or.right(bAndC.right))

      And(aOrB, aOrC)
    },
    { h =>
      val aOrb = h.left
      val aOrC = h.right
      aOrb.orElimination[A Or (B And C)](
        a => Or.left(a),
        b =>
          aOrC.orElimination[A Or (B And C)](
            a => Or.left(a),
            c => Or.right(And(b, c))))
    })

  def l7[A <: Expr]: (A Or True.type) Eq True.type = Eq(
    h => h.orElimination(a => True, t => t),
    h => Or.right[A, True.type](h))

  def l9[A <: Expr, B <: Expr, C <: Expr]: (A Or (B Or C)) Eq ((A Or B) Or C) = Eq(
    h => h.orElimination[(A Or B) Or C](a => Or.left(Or.left(a)), bOrC => bOrC.orElimination(b => Or.left(Or.right(b)), c => Or.right(c))),
    h => h.orElimination[A Or (B Or C)](aOrB => aOrB.orElimination(a => Or.left(a), b => Or.right(Or.left(b))), c => Or.right(Or.right(c))))

  def l10[A <: Expr]: (A Or Bottom) Eq A = Eq(
    h => h.orElimination[A](a => a, bottom => Bottom.elimination(bottom)),
    a => Or.left(a))

  def l11[A <: Expr, B <: Expr, C <: Expr]: (A Imply (B And C)) Eq ((A Imply B) And (A Imply C)) = Eq(
    h => {
      val a1 = Imply((a: A) => h.implicationElimination(a).left)
      val a2 = Imply((a: A) => h.implicationElimination(a).right)

      And(a1, a2)
    },
    h => {
      val a1 = h.left
      val a2 = h.right
      Imply((a: A) => And(a1.implicationElimination(a), a2.implicationElimination(a)))
    })

  def l12[A <: Expr]: (A Imply True.type) Eq True.type = Eq(
    h => True,
    h => Imply((a: A) => True))

  def l13[A <: Expr, B <: Expr, C <: Expr]: (A Imply (B Imply C)) Eq ((A And B) Imply C) = Eq(
    h => Imply((h1: A And B) => h.implicationElimination(h1.left).implicationElimination(h1.right)),
    h => Imply((a: A) => Imply((b: B) => h.implicationElimination(And(a, b)))))

  def l16[A <: Expr, B <: Expr, C <: Expr]: ((A And B) Imply C) Eq (A Imply (B Imply C)) = Eq(
    h => Imply((a: A) => Imply((b: B) => h.implicationElimination(And(a, b)))),
    h => Imply((aAndB: A And B) => h.implicationElimination(aAndB.left).implicationElimination(aAndB.right)))

  def l17[C <: Expr]: (True.type Imply C) Eq C = Eq(
    h => h.implicationElimination(True),
    c => Imply((t: True.type) => c))

  def l19[A <: Expr, B <: Expr, C <: Expr]: ((A Or B) Imply C) Eq ((A Imply C) And (B Imply C)) = Eq(
    h => {
      val a1 = Imply((a: A) => h.implicationElimination(Or.left(a)))
      val a2 = Imply((a: B) => h.implicationElimination(Or.right(a)))

      And(a1, a2)
    },
    h => Imply((aOrB: A Or B) =>
      aOrB.orElimination(
        a => h.left.implicationElimination(a),
        b => h.right.implicationElimination(b)
        )))
        
  def l20[C <: Expr]:(Bottom Imply C) Eq True.type = Eq(
      h => True,
      h => Imply((b:Bottom) => Bottom.elimination(b))
  )       
  
  def deMorgan1[A <: Expr, B <: Expr]:(Not[A] And Not[B]) Eq Not[A Or B] = Eq(
    h => Not( (aOrB:A Or B) => aOrB.orElimination( a => h.left.notElimination(a), b => h.right.notElimination(b))),    
    h => {
      val notA = Not( (a:A) => h.notElimination(Or.left(a)))
      val notB = Not( (b:B) => h.notElimination(Or.right(b)))
      And(notA, notB)
    }
  )

  def deMorgan2[A <: Expr, B <: Expr]:(Not[A] Or Not[B]) Imply Not[A And B] = Imply( h => 
    Not( (aAndB:A And B) => h.orElimination( notA => notA.notElimination(aAndB.left), notB => notB.notElimination(aAndB.right))  )    
  )
   
}