// netlist.hpp -- flat structural Verilog subset: parse into bit-level netlist.
// Supported: module/endmodule, input/output/wire decls (with [msb:lsb] buses),
// primitive gates and/or/nand/nor/not/buf/xor/xnor, assign lhs = rhs;
// constants 1'b0/1'b1, bit-selects name[i], escaped identifiers \foo .
#pragma once
#include <cassert>
#include <cctype>
#include <cstdio>
#include <map>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

struct Gate
{
  std::string type; // and,or,nand,nor,not,buf,xor,xnor  (assign -> buf)
  std::string inst;
  int out = -1;         // net id
  std::vector<int> ins; // net ids
};

struct Netlist
{
  std::string modName;
  std::vector<std::string> netName; // id -> name ("1'b0","1'b1" are ids 0,1)
  std::unordered_map<std::string, int> netId; // name -> id
  std::vector<int> pis, pos;                  // bit-level net ids (decl order)
  std::vector<Gate> gates;
  std::map<std::string, std::pair<int, int>> busRange; // base -> (msb,lsb)

  Netlist ()
  {
    getNet ("1'b0");
    getNet ("1'b1");
  }
  int
  getNet (const std::string &n)
  {
    auto it = netId.find (n);
    if (it != netId.end ())
      return it->second;
    int id = (int)netName.size ();
    netName.push_back (n);
    netId.emplace (n, id);
    return id;
  }
  bool
  hasNet (const std::string &n) const
  {
    return netId.count (n) != 0;
  }
};

// ---------------- tokenizer ----------------
namespace vparse
{

struct Tokens
{
  std::vector<std::string> t;
  size_t p = 0;
  const std::string &
  peek () const
  {
    static const std::string kEnd = "<eof>";
    return p < t.size () ? t[p] : kEnd;
  }
  std::string
  next ()
  {
    if (p >= t.size ())
      throw std::runtime_error ("unexpected end of file");
    return t[p++];
  }
  void
  expect (const std::string &s)
  {
    std::string g = next ();
    if (g != s)
      throw std::runtime_error ("expected '" + s + "' got '" + g + "'");
  }
};

inline Tokens
tokenize (const std::string &text)
{
  Tokens tk;
  size_t i = 0, n = text.size ();
  auto isIdent = [] (char c)
    { return std::isalnum ((unsigned char)c) || c == '_' || c == '$'; };
  while (i < n)
    {
      char c = text[i];
      if (std::isspace ((unsigned char)c))
        {
          i++;
          continue;
        }
      if (c == '/' && i + 1 < n && text[i + 1] == '/')
        {
          while (i < n && text[i] != '\n')
            i++;
          continue;
        }
      if (c == '/' && i + 1 < n && text[i + 1] == '*')
        {
          i += 2;
          while (i + 1 < n && !(text[i] == '*' && text[i + 1] == '/'))
            i++;
          i += 2;
          continue;
        }
      if (c == '\\')
        { // escaped identifier: up to whitespace
          size_t j = i + 1;
          while (j < n && !std::isspace ((unsigned char)text[j]))
            j++;
          tk.t.push_back (
              text.substr (i + 1, j - i - 1)); // store without backslash
          i = j;
          continue;
        }
      if (std::isdigit ((unsigned char)c))
        {
          // number, possibly sized constant like 1'b0
          size_t j = i;
          while (j < n && std::isdigit ((unsigned char)text[j]))
            j++;
          if (j < n && text[j] == '\'')
            {
              j++; // '
              if (j < n)
                j++; // base char
              while (j < n && (isIdent (text[j])))
                j++;
            }
          tk.t.push_back (text.substr (i, j - i));
          i = j;
          continue;
        }
      if (isIdent (c))
        {
          size_t j = i;
          while (j < n && isIdent (text[j]))
            j++;
          tk.t.push_back (text.substr (i, j - i));
          i = j;
          continue;
        }
      tk.t.push_back (std::string (1, c));
      i++;
    }
  return tk;
}

inline bool
isNumber (const std::string &s)
{
  for (char c : s)
    if (!std::isdigit ((unsigned char)c))
      return false;
  return !s.empty ();
}

inline std::string
readFile (const std::string &path)
{
  FILE *f = fopen (path.c_str (), "rb");
  if (!f)
    throw std::runtime_error ("cannot open " + path);
  std::string s;
  char buf[1 << 16];
  size_t r;
  while ((r = fread (buf, 1, sizeof buf, f)) > 0)
    s.append (buf, r);
  fclose (f);
  return s;
}

// parse a signal reference: name, name[idx], 1'b0/1'b1
inline std::string
parseRef (Tokens &tk)
{
  std::string name = tk.next ();
  if (name == "1'b0" || name == "1'b1")
    return name;
  if (tk.peek () == "[")
    {
      tk.next ();
      std::string idx = tk.next ();
      if (!isNumber (idx))
        throw std::runtime_error ("bad bit index " + idx);
      tk.expect ("]");
      name += "[" + idx + "]";
    }
  return name;
}

inline Netlist
parse (const std::string &path)
{
  Netlist nl;
  Tokens tk = tokenize (readFile (path));
  tk.expect ("module");
  nl.modName = tk.next ();
  std::vector<std::string> header;
  if (tk.peek () == "(")
    {
      tk.next ();
      while (tk.peek () != ")")
        {
          std::string s = tk.next ();
          if (s != ",")
            header.push_back (s);
        }
      tk.expect (")");
    }
  tk.expect (";");

  auto declare = [&] (const std::string &kind, Tokens &tk)
    {
      int msb = -1, lsb = -1;
      bool bus = false;
      if (tk.peek () == "[")
        {
          tk.next ();
          msb = std::stoi (tk.next ());
          tk.expect (":");
          lsb = std::stoi (tk.next ());
          tk.expect ("]");
          bus = true;
        }
      std::vector<std::string> names;
      while (true)
        {
          names.push_back (tk.next ());
          std::string s = tk.next ();
          if (s == ";")
            break;
          if (s != ",")
            throw std::runtime_error ("bad decl near " + s);
        }
      for (auto &base : names)
        {
          std::vector<int> bits;
          if (bus)
            {
              nl.busRange[base] = { msb, lsb };
              int lo = std::min (msb, lsb), hi = std::max (msb, lsb);
              for (int b = lo; b <= hi; b++)
                bits.push_back (
                    nl.getNet (base + "[" + std::to_string (b) + "]"));
            }
          else
            {
              bits.push_back (nl.getNet (base));
            }
          if (kind == "input")
            for (int b : bits)
              nl.pis.push_back (b);
          else if (kind == "output")
            for (int b : bits)
              nl.pos.push_back (b);
          // "wire": just registers the nets
        }
    };

  static const char *kGates[]
      = { "and", "or", "nand", "nor", "not", "buf", "xor", "xnor" };
  auto isGate = [&] (const std::string &s)
    {
      for (auto g : kGates)
        if (s == g)
          return true;
      return false;
    };

  while (true)
    {
      std::string s = tk.next ();
      if (s == "endmodule")
        break;
      if (s == "input" || s == "output" || s == "wire")
        {
          declare (s, tk);
        }
      else if (s == "assign")
        {
          std::string lhs = parseRef (tk);
          tk.expect ("=");
          std::string rhs = parseRef (tk);
          tk.expect (";");
          Gate g;
          g.type = "buf";
          g.inst = "";
          g.out = nl.getNet (lhs);
          g.ins.push_back (nl.getNet (rhs));
          nl.gates.push_back (g);
        }
      else if (isGate (s))
        {
          Gate g;
          g.type = s;
          if (tk.peek () != "(")
            g.inst = tk.next ();
          tk.expect ("(");
          std::vector<std::string> args;
          while (true)
            {
              args.push_back (parseRef (tk));
              std::string d = tk.next ();
              if (d == ")")
                break;
              if (d != ",")
                throw std::runtime_error ("bad gate arg near " + d);
            }
          tk.expect (";");
          if (args.size () < 2)
            throw std::runtime_error ("gate with <2 args");
          g.out = nl.getNet (args[0]);
          for (size_t k = 1; k < args.size (); k++)
            g.ins.push_back (nl.getNet (args[k]));
          if ((g.type == "not" || g.type == "buf") && g.ins.size () != 1)
            throw std::runtime_error ("not/buf must have 1 input");
          nl.gates.push_back (g);
        }
      else
        {
          throw std::runtime_error ("unexpected token '" + s + "'");
        }
    }
  return nl;
}

} // namespace vparse
