package com.github.gdefacci.constructive

sealed trait Expr 

case object True extends Expr

sealed trait Bottom extends Expr

object Bottom {
  
  def elimination[C <: Expr](b:Bottom):C = ???
}

final case class And[A <: Expr, B <: Expr](left: A, right: B) extends Expr 

object Or {
  
  def left[A <: Expr,B <: Expr](a:A) = Or[A,B](Left(a))
  def right[A <: Expr,B <: Expr](b:B) = Or[A,B](Right(b))
  
}

final case class Or[A <: Expr, B <: Expr] private (private val disj:Either[A,B]) extends Expr {
  
  def orElimination[C <: Expr](caseA:A => C, caseB:B => C):C = {
    disj.fold(caseA, caseB)
  }
  
}

final case class Imply[A <: Expr, B <: Expr] (implicationElimination:A => B) extends Expr

final case class Not[A](notElimination:A => Bottom) extends Expr

final case class Eq[A <: Expr, B <: Expr](direct:A => B, inverse:B => A)