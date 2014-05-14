package hampi.experiments;

import hampi.utils.Files;

import java.io.IOException;
import java.util.*;

public class BigTable{

  private final List<List<String>> cellsInRows = new ArrayList<List<String>>();
  public static BigTable readFromFile(String fileName) throws IOException{
    List<String> rows = Files.readWhole(fileName);
    BigTable bt = new BigTable();
    for (String row : rows){
      bt.addRow(row);
    }
    return bt;
  }

  private void addRow(String row){
    cellsInRows.add(Arrays.asList(row.split(" ")));
  }

  public int rowCount(){
    return cellsInRows.size();
  }

  public int columnCount(int row){
    return cellsInRows.get(row).size();
  }

  public String cell(int row, int column) {
    return cellsInRows.get(row).get(column);
  }

  @Override
  public String toString(){
    StringBuilder b = new StringBuilder();
    for (List<String> row : cellsInRows){
      for (String cell : row){
        b.append(cell).append(" ");
      }
      b.append("\n");
    }
    return b.toString();
  }

  /**
   * Returns the row as a list of ints.
   */
  public List<Integer> intRow(int row){
    List<Integer> result = new ArrayList<Integer>();
    for (String rowCell : cellsInRows.get(row)){
      result.add(Integer.valueOf(rowCell));
    }
    return result;
  }

  public List<Integer> intColumn(int column){
    List<Integer> result = new ArrayList<Integer>(rowCount());
    for (int i = 0; i < rowCount(); i++){
      result.add(intCell(i, column));
    }
    return result;
  }


  public int intCell(int row, int column){
    return Integer.valueOf(cell(row, column));
  }
}
