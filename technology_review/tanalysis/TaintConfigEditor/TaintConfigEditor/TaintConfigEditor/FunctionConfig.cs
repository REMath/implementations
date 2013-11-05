using System;
using System.Collections.Generic;
using System.Text;
using System.IO;

namespace TaintConfigEditor
{
    public enum TaintTypes 
    {
        U, 
        T,
        G
    }

    public enum Types
    {
        INT,
        VOID,
        PTR,
        FLOAT
    }

    public class Taint
    {
        public TaintTypes taintType;
        private IList<string> taintDependencies = new List<string> ();

        public Taint(TaintTypes tt)
        {
            taintType = tt;
        }

        public IList<string> getDependencies() {
            if (taintType != TaintTypes.G)
                throw new InvalidOperationException();
            return taintDependencies;
        }
    }

    public class FunctionConfig
    {
        public class Param 
        {
            public string name;
            public Types paramType;
            public Taint paramTaint;
        }
        public string name;
        public Types returnType;
        public Taint returnTaint;
        public IList<Param> parameters;

        public FunctionConfig(string fname, Types retType, Taint retTaint, IList<Param> param)
        {
            name = fname;
            returnType = retType;
            returnTaint = retTaint;
            parameters = param;
            CheckFunction();
        }

        private void CheckDependency(IList<string> deps)
        {
            foreach (string dep in deps)
            {
                bool exists = false;
                foreach (Param param in parameters)
                {
                    if (param.name.Equals(dep))
                    {
                        exists = true;
                        break;
                    }
                }
                if (!exists)
                    throw new InvalidOperationException("Unable to find dependency " + dep + " for function " + name);
            }
        }

        private void CheckFunction()
        {
            if (returnTaint.taintType == TaintTypes.G)
            {
                CheckDependency(returnTaint.getDependencies());
            }
            foreach (Param p in parameters)
            {
                if (p.paramTaint.taintType == TaintTypes.G)
                {
                    CheckDependency(p.paramTaint.getDependencies());
                }
            }
        }

        private static string StripWS(string s)
        {
            string result = s;
            int index = result.IndexOf('\n');
            if (index >= 0)
                result = result.Substring(0, index);
            index = result.IndexOf('\r');
            if (index >= 0)
                result = result.Substring(0, index);
            index = result.IndexOf(' ');
            if (index >= 0)
                result = result.Substring(0, index);
            index = result.IndexOf('\t');
            if (index >= 0)
                result = result.Substring(0, index);
            index = result.IndexOf('#');
            if (index >= 0)
                result = result.Substring(0, index);
            return result;
        }

        private static string AddComment(string s, string comment)
        {
            return s + "\t\t\t#" + comment;
        }

        private static string ReadStr(StreamReader reader)
        {
            return StripWS(reader.ReadLine());
        }

        private static int ReadInt(StreamReader reader)
        {
            return Int32.Parse(ReadStr(reader));
        }

        public static TaintTypes TaintFromStr(string taintStr)
        {
            switch (taintStr)
            {
                case "U":
                    return TaintTypes.U;
                case "T":
                    return TaintTypes.T;
                case "G":
                    return TaintTypes.G;
                default:
                    throw new InvalidOperationException("Invalid taint string");
            }
        }

        public static string StrFromTaint(TaintTypes tt)
        {
            switch (tt)
            {
                case TaintTypes.G:
                    return "G";
                case TaintTypes.T:
                    return "T";
                case TaintTypes.U:
                    return "U";
                default:
                    throw new InvalidOperationException();
            }
        }

        public static Types TypeFromStr(string typeStr)
        {
            switch (typeStr)
            {
                case "float":
                    return Types.FLOAT;
                case "int":
                    return Types.INT;
                case "void":
                    return Types.VOID;
                case "ptr":
                    return Types.PTR;
                default:
                    throw new InvalidOperationException("Invalid type string");
            }
        }

        public static string StrFromType(Types t)
        {
            switch (t)
            {
                case Types.FLOAT:
                    return "float";
                case Types.INT:
                    return "int";
                case Types.PTR:
                    return "ptr";
                case Types.VOID:
                    return "void";
                default:
                    throw new InvalidOperationException();
            }
        }

        private static FunctionConfig builfFunctionConfig(StreamReader reader)
        {
            ReadStr(reader);
            ReadStr(reader);
            string fname = ReadStr(reader);
            Types retType = TypeFromStr(ReadStr(reader));
            Taint retTaint = new Taint(TaintFromStr(ReadStr(reader)));
            int retDepsCount = ReadInt(reader);
            for (int i = 0; i < retDepsCount; ++i)
            {
                string retDepName = ReadStr(reader);
                retTaint.getDependencies().Add(retDepName);
            }
            int paramCount = ReadInt(reader);
            IList<Param> parameters = new List<Param>();
            for (int i = 0; i < paramCount; ++i)
            {
                ReadStr(reader);
                string paramName = ReadStr(reader);
                Types paramType = TypeFromStr(ReadStr(reader));
                Taint paramTaint = new Taint(TaintFromStr(ReadStr(reader)));
                int paramDepsCount = ReadInt(reader);
                for (int j = 0; j < paramDepsCount; ++j)
                {
                    string paramDepName = ReadStr(reader);
                    paramTaint.getDependencies().Add(paramDepName);
                }
                Param newParam = new Param();
                newParam.name = paramName;
                newParam.paramTaint = paramTaint;
                newParam.paramType = paramType;
                parameters.Add(newParam);
            }
            return new FunctionConfig(fname, retType, retTaint, parameters);
        }

        public static List<FunctionConfig> buildFunctionConfigs(string filename)
        {
            using (StreamReader reader = new StreamReader(filename))
            {
                List<FunctionConfig> result = new List<FunctionConfig>();
                int functionCount = ReadInt(reader);
                for (int i = 0; i < functionCount; ++i)
                {
                    result.Add(builfFunctionConfig(reader));
                }
                return result;
            }
        }

        private static void writeFunctionConfigs(StreamWriter writer, FunctionConfig func)
        {
            writer.WriteLine();
            writer.WriteLine("++++++++++");
            writer.WriteLine(AddComment(func.name, "function name"));
            writer.WriteLine(AddComment(StrFromType(func.returnType), "function return type"));
            writer.WriteLine(AddComment(StrFromTaint(func.returnTaint.taintType), "function return taint"));
            int retDepCount = 0;
            if (func.returnTaint.taintType == TaintTypes.G)
            {
                retDepCount = func.returnTaint.getDependencies().Count;
            }
            writer.WriteLine(AddComment(retDepCount.ToString(), "function return deps count"));
            for (int i = 0; i < retDepCount; ++i)
            {
                writer.WriteLine(AddComment(func.returnTaint.getDependencies()[i], "function return dep " + i));
            }
            writer.WriteLine(AddComment(func.parameters.Count.ToString(), "function param count"));
            foreach(Param param in func.parameters) 
            {
                writer.WriteLine("==========");
                writer.WriteLine(AddComment(param.name, "param name"));
                writer.WriteLine(AddComment(StrFromType(param.paramType), "param type"));
                writer.WriteLine(AddComment(StrFromTaint(param.paramTaint.taintType), "param taint"));
                int paramDepCount = 0;
                if (param.paramTaint.taintType == TaintTypes.G)
                {
                    paramDepCount = param.paramTaint.getDependencies().Count;
                }
                writer.WriteLine(AddComment(paramDepCount.ToString(), "param deps count"));
                for (int i = 0; i < paramDepCount; ++i)
                {
                    writer.WriteLine(AddComment(param.paramTaint.getDependencies()[i], "param dep " + i));
                }
            }
        }

        public static void writeFunctionConfigs(string filename, IList<FunctionConfig> funcs)
        {
            using (StreamWriter writer = new StreamWriter(filename))
            {
                writer.WriteLine(funcs.Count.ToString());
                foreach (FunctionConfig func in funcs)
                {
                    writeFunctionConfigs(writer, func);
                }
            }
        }

    }
}
