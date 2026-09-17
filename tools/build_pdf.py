"""Typeset the distributed Markdown paper with standard LaTeX; no network calls.

Requirements: Python 3, pdflatex, and the LaTeX packages in PREAMBLE.
The small converter handles the manuscript's headings, paragraphs, math,
emphasis, links, lists, and table. It preserves TeX mathematics verbatim.
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
PREAMBLE=r'''\documentclass[11pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{lmodern}
\usepackage{amsmath,amssymb}
\usepackage[margin=26mm,headheight=14pt]{geometry}
\usepackage{microtype}
\usepackage{booktabs,tabularx,array}
\usepackage{xcolor}
\usepackage{enumitem}
\usepackage{fancyhdr}
\usepackage{needspace}
\usepackage[unicode,breaklinks=true]{hyperref}
\hypersetup{pdftitle={The Third Borwein Conjecture for n >= 31147},
 pdfauthor={},pdfsubject={Coefficient signs and zero classification for n >= 31147},
 pdfkeywords={Third Borwein conjecture, q-series, saddle point, Lean},
 colorlinks=true,linkcolor=black,urlcolor=blue!45!black,citecolor=black}
\pdfinfoomitdate=1
\pdftrailerid{}
\pdfsuppressptexinfo=15
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small The Third Borwein Conjecture}
\fancyhead[R]{\small $n\ge31{,}147$}
\fancyfoot[C]{\thepage}
\renewcommand{\headrulewidth}{0.3pt}
\setlength{\parindent}{0pt}
\setlength{\parskip}{6pt plus 1pt minus 1pt}
\setlength{\emergencystretch}{2em}
\setlist{nosep,leftmargin=1.5em,topsep=4pt}
\setcounter{tocdepth}{1}
\widowpenalty=10000
\clubpenalty=10000
\newcolumntype{Y}{>{\raggedright\arraybackslash}X}
\begin{document}
'''

ESC={'&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_',
     '{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}',
     '\\':r'\textbackslash{}','≤':r'\ensuremath{\le}',
     '≥':r'\ensuremath{\ge}','∉':r'\ensuremath{\notin}',
     'ℕ':r'\ensuremath{\mathbb{N}}','→':r'\ensuremath{\to}',
     '–':'--','—':'---','−':'-','’':"'",'“':'``','”':"''"}
def escape(s): return ''.join(ESC.get(c,c) for c in s)

TOKEN=re.compile(r'(`[^`]+`|\$[^$]+\$|\*\*.+?\*\*|\*[^*]+\*|\[[^\]]+\]\([^)]+\))')
def inline(s):
    parts=[];last=0
    for match in TOKEN.finditer(s):
        parts.append(escape(s[last:match.start()]));token=match.group()
        if token.startswith('`'):
            value=escape(token[1:-1]).replace('.',r'.\allowbreak ').replace(r'\_',r'\_\allowbreak ')
            parts.append(r'\texttt{'+value+'}')
        elif token.startswith('$'): parts.append(token)
        elif token.startswith('**'): parts.append(r'\textbf{'+inline(token[2:-2])+'}')
        elif token.startswith('*'): parts.append(r'\emph{'+inline(token[1:-1])+'}')
        else:
            label,url=re.fullmatch(r'\[([^\]]+)\]\(([^)]+)\)',token).groups()
            parts.append(r'\href{'+url.replace('%',r'\%').replace('#',r'\#')+'}{'+inline(label)+'}')
        last=match.end()
    parts.append(escape(s[last:]))
    return ''.join(parts)

def render(markdown):
    lines=markdown.splitlines();out=[PREAMBLE];i=0
    while i<len(lines):
        line=lines[i].strip()
        if not line: i+=1;continue
        if line.startswith('# '):
            out.append(r'\begin{center}\LARGE\bfseries '+inline(line[2:])+r'\par\end{center}\vspace{3mm}\thispagestyle{plain}')
            i+=1;continue
        if line.startswith('## '):
            heading=line[3:]
            if heading=='Abstract':out.append(r'\subsection*{Abstract}')
            else:
                heading=re.sub(r'^\d+\.\s*','',heading)
                command='section' if re.match(r'\d+\.',line[3:]) else 'section*'
                if heading=='Supporting Lean verification':out.append(r'\clearpage')
                out.append(r'\Needspace{5\baselineskip}'+'\\'+command+'{'+inline(heading)+'}')
            i+=1;continue
        if line=='$$':
            j=i+1
            while j<len(lines) and lines[j].strip()!='$$':j+=1
            if j==len(lines):raise ValueError('Unclosed display math')
            out.append('\\begin{equation*}\n'+'\n'.join(lines[i+1:j])+'\n\\end{equation*}')
            i=j+1;continue
        if line.startswith('|'):
            rows=[]
            while i<len(lines) and lines[i].strip().startswith('|'):
                row=[x.strip() for x in lines[i].strip().strip('|').split('|')]
                if not all(re.fullmatch(r'[:\- ]+',c) for c in row):rows.append(row)
                i+=1
            out.append(r'\begin{center}\small\renewcommand{\arraystretch}{1.2}\begin{tabularx}{\textwidth}{@{}>{\raggedright\arraybackslash}p{0.24\textwidth}Y>{\raggedright\arraybackslash}p{0.23\textwidth}@{}}\toprule')
            for k,row in enumerate(rows):
                cells=[inline(x) for x in row]
                if k==0:cells=[r'\textbf{'+x+'}' for x in cells]
                out.append(' & '.join(cells)+r' \\')
                if k==0:out.append(r'\midrule')
            out.append(r'\bottomrule\end{tabularx}\end{center}')
            continue
        if re.match(r'^(?:\d+\. |[-*] )',line):
            ordered=bool(re.match(r'^\d+\. ',line));env='enumerate' if ordered else 'itemize'
            out.append(r'\begin{'+env+'}')
            while i<len(lines) and re.match(r'^(?:\d+\. |[-*] )',lines[i].strip()):
                item=re.sub(r'^(?:\d+\. |[-*] )','',lines[i].strip())
                out.append(r'\item '+inline(item));i+=1
            out.append(r'\end{'+env+'}');continue
        para=[line];i+=1
        while i<len(lines) and lines[i].strip() and not re.match(r'^(?:#|\$\$|\||\d+\. |[-*] )',lines[i].strip()):
            para.append(lines[i].strip());i+=1
        next_line=i
        while next_line<len(lines) and not lines[next_line].strip():next_line+=1
        if next_line<len(lines) and lines[next_line].strip()=='$$':
            out.append(r'\Needspace{7\baselineskip}')
        out.append(inline(' '.join(para))+'\n')
    out.append(r'\end{document}')
    return '\n\n'.join(out)+'\n'

def main():
    binary=shutil.which('pdflatex')
    if not binary:raise RuntimeError('pdflatex is required (TeX Live with the packages listed in PREAMBLE).')
    build=ROOT/'.pdf-build';build.mkdir(exist_ok=True)
    tex=build/'paper.tex'
    tex.write_text(render((ROOT/'paper.md').read_text(encoding='utf-8')),encoding='utf-8')
    for pass_number in [1,2]:
        command=[binary,'-no-shell-escape','-interaction=nonstopmode','-halt-on-error',
            '-file-line-error','-output-directory',str(build),str(tex)]
        result=subprocess.run(command,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (build/f'pass-{pass_number}.log').write_bytes(result.stdout)
        if result.returncode:
            sys.stderr.write(result.stdout.decode('utf-8',errors='replace'))
            raise RuntimeError('PDF typesetting failed')
    shutil.copyfile(build/'paper.pdf',ROOT/'paper.pdf')
    print('Created paper.pdf from paper.md; intermediate files are in .pdf-build.')

if __name__=='__main__':main()
