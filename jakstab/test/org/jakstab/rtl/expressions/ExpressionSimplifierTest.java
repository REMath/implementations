package org.jakstab.rtl.expressions;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

public class ExpressionSimplifierTest {

	private ExpressionSimplifier simplifier;
	RTLVariable eax;
	RTLVariable ebx;
	RTLExpression five;
	RTLExpression eaxPlusEbx;
	
	@Before
	public void setUp() throws Exception {
		simplifier = ExpressionSimplifier.getInstance();
		eax = ExpressionFactory.createVariable("eax", 32);
		ebx = ExpressionFactory.createVariable("ebx", 32);
		five = ExpressionFactory.createNumber(5, 32);
		eaxPlusEbx = ExpressionFactory.createPlus(eax, ebx);
	}
	

	@Test
	public void doNotModifySingleVariable() {
		assertEquals(eax, simplifier.simplify(eax));
	}
	
	@Test
	public void substitute() {

		RTLExpression e = ExpressionFactory.createOr(ExpressionFactory.createLessThan(eax, five),
				ExpressionFactory.createEqual(eax, five));
		assertEquals(ExpressionFactory.createLessOrEqual(eax, five), simplifier.simplify(e));
		
		e = ExpressionFactory.createOr(ExpressionFactory.createLessThan(eax, eaxPlusEbx),
				ExpressionFactory.createEqual(eax, eaxPlusEbx));
		assertEquals(ExpressionFactory.createLessOrEqual(eax, eaxPlusEbx), simplifier.simplify(e));
	}
	
	@Test
	public void innerSubstitute() {
		RTLExpression e1 = ExpressionFactory.createOr(ExpressionFactory.createLessThan(eax, five),
				ExpressionFactory.createEqual(eax, five));
		RTLExpression e2 = ExpressionFactory.createOr(ExpressionFactory.createLessThan(eax, eaxPlusEbx),
				ExpressionFactory.createEqual(eax, eaxPlusEbx));
		RTLExpression e = ExpressionFactory.createAnd(e1, e2);
		
		assertEquals(ExpressionFactory.createAnd(
				ExpressionFactory.createLessOrEqual(eax, five),
				ExpressionFactory.createLessOrEqual(eax, eaxPlusEbx)),
				simplifier.simplify(e));
		
	}
	
	@Test
	public void complexSubstitute() {
		RTLExpression fiftyEight = ExpressionFactory.createNumber(58, 32); 
		RTLExpression eaxMinus58 = ExpressionFactory.createMinus(eax, fiftyEight);
		RTLExpression num0 = ExpressionFactory.createNumber(0, 32); 
		
		RTLExpression e = ExpressionFactory.createAnd(
				ExpressionFactory.createEqual(
						ExpressionFactory.createLessThan(eaxMinus58, num0),
						ExpressionFactory.createAnd(
								ExpressionFactory.createLessThan(num0, eaxMinus58),
								ExpressionFactory.createLessThan(eax, num0)
								)),
				ExpressionFactory.createNotEqual(eax, fiftyEight));
		System.out.println("Expression to simplify: " + e);
		
		RTLExpression result = simplifier.simplify(e);
		
		assertNotSame(result, e);
		
		assertEquals(ExpressionFactory.createLessThan(fiftyEight, eax), result);
	}
	
	@Test
	public void bitwidths() {
		RTLExpression e = ExpressionFactory.createOr(ExpressionFactory.createLessThan(eax, five),
				ExpressionFactory.createEqual(eax, five));
		assertEquals(1, simplifier.simplify(e).getBitWidth());
		
		e = ExpressionFactory.createOr(eax, eax);
		assertEquals(eax.getBitWidth(), simplifier.simplify(e).getBitWidth());
	}

}
