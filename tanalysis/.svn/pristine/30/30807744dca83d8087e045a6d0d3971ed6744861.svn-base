using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace TaintConfigEditor
{
    public partial class FunctionEditor : Form
    {
        public FunctionConfig function = null;

        public FunctionEditor()
        {
            InitializeComponent();
            InitFields();
        }

        private void InitCombos()
        {
            comboTaint.DataSource = new List<string>() { "U", "T", "G" };
            comboType.DataSource = new List<string>() { "void", "int", "ptr", "float" };
        }

        private void InitGrid()
        {
            dgParams.AutoGenerateColumns = false;
            var pNameColumn = new DataGridViewTextBoxColumn();
            pNameColumn.Name = "Name";
            dgParams.Columns.Add(pNameColumn);
            var pTypeColumn = new DataGridViewComboBoxColumn();
            pTypeColumn.DataSource = new List<string>() { "void", "int", "ptr", "float" };
            pTypeColumn.Name = "Type";
            dgParams.Columns.Add(pTypeColumn);
            var pTaintColumn = new DataGridViewComboBoxColumn();
            pTaintColumn.DataSource = new List<string>() { "U", "T", "G" };
            pTaintColumn.Name = "Taint";
            dgParams.Columns.Add(pTaintColumn);
            var pDepsColumn = new DataGridViewTextBoxColumn();
            pDepsColumn.Name = "Deps";
            dgParams.Columns.Add(pDepsColumn);
        }

        private void InitFields()
        {
            InitCombos();
            InitGrid();
        }

        private void btnOk_Click(object sender, EventArgs e)
        {
            try
            {
                string fname = tbFname.Text;
                Types returnType = FunctionConfig.TypeFromStr((string)comboType.SelectedItem);
                TaintTypes returnTaintType = FunctionConfig.TaintFromStr((string)comboTaint.SelectedItem);
                Taint returnTaint = new Taint(returnTaintType);
                if (returnTaintType == TaintTypes.G)
                {
                    string[] returnDepNames = tbReturnDeps.Text.Split(new char[] { ' ' });
                    foreach (string retDep in returnDepNames)
                    {
                        returnTaint.getDependencies().Add(retDep);
                    }
                }
                IList<FunctionConfig.Param> parameters = new List<FunctionConfig.Param>();
                foreach (DataGridViewRow row in dgParams.Rows)
                {
                    if (row.IsNewRow)
                        continue;
                    string pName = (string)row.Cells["Name"].Value;
                    Types pType = FunctionConfig.TypeFromStr((string)row.Cells["Type"].Value);
                    TaintTypes pTaintType = FunctionConfig.TaintFromStr((string)row.Cells["Taint"].Value);
                    Taint pTaint = new Taint(pTaintType);
                    if (pTaintType == TaintTypes.G)
                    {
                        string[] paramDepNames = ((string)row.Cells["Deps"].Value).Split(new char[] { ' ' });
                        foreach (string paramDep in paramDepNames)
                        {
                            pTaint.getDependencies().Add(paramDep);
                        }
                    }
                    FunctionConfig.Param param = new FunctionConfig.Param();
                    param.name = pName;
                    param.paramType = pType;
                    param.paramTaint = pTaint;
                    parameters.Add(param);
                }

                function = new FunctionConfig(fname, returnType, returnTaint, parameters);
            }
            catch (InvalidOperationException)
            {
                MessageBox.Show("Function cannot be added! Invalid dependencies");
                this.DialogResult = DialogResult.Cancel;
            }
        }


    }
}
