using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Text;
using System.Windows.Forms;

namespace TaintConfigEditor
{
    public partial class Form1 : Form
    {
        private List<FunctionConfig> functions = null;
        private string filename = null;

        public Form1()
        {
            InitializeComponent();
        }

        private void btnSaveConfig_Click(object sender, EventArgs e)
        {
            FunctionConfig.writeFunctionConfigs(filename, functions);
            MessageBox.Show("New configuration saved to " + filename);
        }

        private void btnAddFunction_Click(object sender, EventArgs e)
        {
            FunctionEditor fe = new FunctionEditor();
            if (fe.ShowDialog() == DialogResult.OK)
            {
                var newFunc = fe.function;
                if (!CheckNewFunc(newFunc))
                {
                    MessageBox.Show("Function " + newFunc.name + " already in configuration file");
                    return;
                }
                functions.Add(newFunc);
                MessageBox.Show("Function " + newFunc.name + " added");
            }
        }

        private bool CheckNewFunc(FunctionConfig newFunc)
        {
            bool found = false;
            foreach (FunctionConfig f in functions)
            {
                if (f.name.Equals(newFunc.name))
                {
                    found = true;
                    break;
                }
            }
            if (found)
                return false;
            return true;
        }

        private void Form1_Load(object sender, EventArgs e)
        {
            while (true) 
            {
                if (openConfigFileDialog.ShowDialog() == DialogResult.OK)
                    break;
            }
            filename = openConfigFileDialog.FileName;
            functions = FunctionConfig.buildFunctionConfigs(filename);
            MessageBox.Show("LOADED");
        }
    }
}
