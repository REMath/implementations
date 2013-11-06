package hampi.stp;

import java.util.*;

public abstract class ChoiceGenerator<T> {
  /**
   * Returns the sublist of selected elements.
   */
  public abstract List<T> choose(List<T> ts);

  public abstract boolean isDone();

  public abstract void reset();

  //----------------------------------------------------
  public static <T> ChoiceGenerator<T> createFull(){
    return new ChoiceGenerator<T>(){

      private boolean isDone = false;

      @Override
      public List<T> choose(List<T> list){
        if (isDone())
          throw new IllegalStateException("do not call if the generator isDone");
        return list;//simply return the list
      }

      @Override
      public boolean isDone(){
        return isDone;
      }

      @Override
      public void reset(){
        isDone = true;
      }
    };
  }

  //-----------------------------------------------
  /**
   * Creates a generator that gives list elements one by one.
   */
  public static <T> ChoiceGenerator<T> createOneByOne(){
    return new ChoiceGenerator<T>(){

      private final List<List<T>> lists = new ArrayList<List<T>>();
      private final List<Integer> indices = new ArrayList<Integer>();//current pointers in the lists

      private int listIndex = 0;//which list is current
      private boolean isReset = false;

      @Override
      public List<T> choose(List<T> ts){
        //        System.out.println("choose");
        if (ts.isEmpty())
          throw new IllegalArgumentException("empty list");
        if (lists.size() < listIndex)
          throw new IllegalStateException();
        if (lists.size() == listIndex && lists.size() != indices.size())
          throw new IllegalStateException();

        if (lists.size() == listIndex){//new list
          lists.add(ts);
          listIndex++;
          indices.add(1);
          return Collections.singletonList(ts.get(0));
        }

        if (lists.get(listIndex) != ts)//we've not seen this list before
          throw new IllegalStateException("expected a different list");

        if (isTailDone()){//last list of the trailing lists have no more choices
          int idx = indices.get(listIndex);
          indices.set(listIndex, idx + 1);//increment the index
          for (int i = indices.size() - 1; i >= listIndex + 1; i--){
            indices.remove(i);//delete all subsequent lists
            lists.remove(i);
          }
          listIndex++;
          return Collections.singletonList(ts.get(idx));
        }else{//return whatever we returned last time - the next list will change the choice
          int idx = indices.get(listIndex);
          listIndex++;
          return Collections.singletonList(ts.get(idx - 1));
        }
      }

      /**
       * Returns whether all options for lists after the current one are
       * exhausted.
       */
      private boolean isTailDone(){
        if (lists.size() == listIndex + 1)
          return true;
        for (int i = listIndex + 1; i < lists.size(); i++){
          if (indices.get(i) != lists.get(i).size())
            return false;
        }
        return true;
      }

      @Override
      public boolean isDone(){
        //                System.out.println("isDone");
        if (!isReset)
          return false;
        for (int i = 0; i < lists.size(); i++){
          if (lists.get(i).size() != indices.get(i))
            return false;
        }
        return true;
      }

      @Override
      public void reset(){
        //                                System.out.println("reset:" + indices);
        //        for (int i = 0; i < lists.size(); i++){
        //          System.out.print(indices.get(i) + ":" + lists.get(i).size() + " ");
        //        }
        //        System.out.println(" ");
        listIndex = 0;
        isReset = true;
      }

      @Override
      public String toString(){
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < lists.size(); i++){
          if (i == listIndex){
            b.append("[");
          }
          b.append(indices.get(i)).append(":").append(lists.get(i).size());
          if (i == listIndex){
            b.append("]");
          }
          b.append(" ");
        }
        return b.toString();
      }
    };
  }
}
