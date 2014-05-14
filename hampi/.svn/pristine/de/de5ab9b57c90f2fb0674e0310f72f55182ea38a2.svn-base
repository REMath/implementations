package hampi.tests;

import hampi.stp.ChoiceGenerator;

import java.util.*;

import junit.framework.TestCase;

public class ChoiceGeneratorTests extends TestCase{
  public void testFull1() throws Exception{
    ChoiceGenerator<Integer> cgFull = ChoiceGenerator.<Integer>createFull();
    assertTrue(!cgFull.isDone());
    cgFull.reset();
    assertTrue(cgFull.isDone());
  }

  public void testFull2() throws Exception{
    ChoiceGenerator<Integer> cgFull = ChoiceGenerator.<Integer>createFull();
    List<Integer> l123 = Arrays.asList(1, 2, 3);
    List<Integer> choose123 = cgFull.choose(l123);
    assertEquals(l123, choose123);

    List<Integer> l1234 = Arrays.asList(1, 2, 3, 4);
    List<Integer> choose1234 = cgFull.choose(l1234);
    assertEquals(l1234, choose1234);

    cgFull.reset();
    assertTrue(cgFull.isDone());
    try {
      choose123 = cgFull.choose(l123);
      fail("expected an exception");
    }catch (IllegalStateException e){
      //ok
    }
  }

  public void testFull3() throws Exception{
    ChoiceGenerator<Integer> cgFull = ChoiceGenerator.<Integer>createFull();
    List<Integer> l123 = Arrays.asList(1, 2, 3);
    List<Integer> choose123 = cgFull.choose(l123);
    assertEquals(l123, choose123);

    //call again on same list is ok
    choose123 = cgFull.choose(l123);
    assertEquals(l123, choose123);

    cgFull.reset();
    assertTrue(cgFull.isDone());
    try{
      choose123 = cgFull.choose(l123);
      fail("expected an exception");
    }catch (IllegalStateException e){
      //ok
    }
  }

  public void testOneByOne1() throws Exception{
    ChoiceGenerator<Integer> cgOne = ChoiceGenerator.<Integer>createOneByOne();
    assertTrue(!cgOne.isDone());
    cgOne.reset();
    assertTrue(cgOne.isDone());
  }

  public void testOneByOne2() throws Exception{
    ChoiceGenerator<Integer> cgOne = ChoiceGenerator.<Integer>createOneByOne();
    assertTrue(!cgOne.isDone());

    List<Integer> l12 = Arrays.asList(1, 2);
    List<Integer> choose = cgOne.choose(l12);
    assertEquals(Arrays.asList(1), choose);

    cgOne.reset();
    assertTrue(!cgOne.isDone());//not done, there are more choices in the first list
  }

  public void testOneByOne3() throws Exception{
    ChoiceGenerator<Integer> cgOne = ChoiceGenerator.<Integer>createOneByOne();
    assertTrue(!cgOne.isDone());

    List<Integer> l12 = Arrays.asList(1, 2);
    List<Integer> choose1 = cgOne.choose(l12);
    assertEquals(Arrays.asList(1), choose1);

    cgOne.reset();
    assertTrue(!cgOne.isDone());//not done, there are more choices in the list

    List<Integer> choose2 = cgOne.choose(l12);
    assertEquals(Arrays.asList(2), choose2);

    cgOne.reset();
    assertTrue(cgOne.isDone());//done, no more choices in the list
  }

  public void testOneByOne4() throws Exception{
    ChoiceGenerator<Integer> cgOne = ChoiceGenerator.<Integer>createOneByOne();
    assertTrue(!cgOne.isDone());

    //we have 2 list, each with 2 elements. We want to explore the space in 4 iterations

    //first iter
    List<Integer> l12 = Arrays.asList(1, 2);
    List<Integer> choose12_1 = cgOne.choose(l12);
    assertEquals(Arrays.asList(1), choose12_1);

    List<Integer> l34 = Arrays.asList(3, 4);
    List<Integer> choose34_1 = cgOne.choose(l34);
    assertEquals(Arrays.asList(3), choose34_1);

    cgOne.reset();
    assertTrue(!cgOne.isDone());

    //2nd iter
    List<Integer> choose12_2 = cgOne.choose(l12);
    assertEquals(Arrays.asList(1), choose12_2);//this choice is the same as on the first round because the next list has more choices

    List<Integer> choose34_2 = cgOne.choose(l34);
    assertEquals(Arrays.asList(4), choose34_2);

    cgOne.reset();
    assertTrue(!cgOne.isDone());

    //3rd iter
    List<Integer> choose12_3 = cgOne.choose(l12);
    assertEquals(Arrays.asList(2), choose12_3);//now the choice advances here

    List<Integer> choose34_3 = cgOne.choose(l34);
    assertEquals(Arrays.asList(3), choose34_3);//back to the first choice here

    cgOne.reset();
    assertTrue(!cgOne.isDone());

    //4th iter
    List<Integer> choose12_4 = cgOne.choose(l12);
    assertEquals(Arrays.asList(2), choose12_4);//stay here

    List<Integer> choose34_4 = cgOne.choose(l34);
    assertEquals(Arrays.asList(4), choose34_4);//advance here

    cgOne.reset();
    assertTrue(cgOne.isDone());//done, no more choices in the lists
  }

}
