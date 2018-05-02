from docutils import nodes
from docutils.parsers.rst import Directive
from sphinx.builders import Builder
from sphinx.directives import CodeBlock
from sphinx.errors import SphinxError
import os, os.path, fnmatch, subprocess
import codecs
import urllib
import re

try:
    urlquote = urllib.parse.quote
except:
    # Python 2
    def urlquote(s, safe='/'):
        return urllib.quote(s.encode('utf-8'), safe)


# "Try it!" button

class lean_code_goodies(nodes.General, nodes.Element): pass

def mk_try_it_uri(code):
    uri = 'https://leanprover.github.io/live/3.4.1/#code='
    uri += urlquote(code, safe='~@#$&()*!+=:;,.?/\'')
    return uri

def process_lean_nodes(app, doctree, fromdocname):
    for node in doctree.traverse(nodes.literal_block):
        if node['language'] != 'lean': continue

        new_node = lean_code_goodies()
        new_node['full_code'] = node.rawsource
        node.replace_self([new_node])

        code = node.rawsource
        m = re.search(r'--[^\n]*BEGIN[^\n]*\n(.*)--[^\n]*END', code, re.DOTALL)
        if m:
            node = nodes.literal_block(m.group(1), m.group(1))
            node['language'] = 'lean'
        new_node += node

        if app.builder.name.startswith('epub'):
            new_node.replace_self([node])

def html_visit_lean_code_goodies(self, node):
    self.body.append(self.starttag(node, 'div', style='position: relative'))
    self.body.append("<div style='position: absolute; right: 0; top: 0; padding: 1ex'>")
    self.body.append(self.starttag(node, 'a', target='_blank', href=mk_try_it_uri(node['full_code'])))
    self.body.append('try it!</a></div>')

def html_depart_lean_code_goodies(self, node):
    self.body.append('</div>')

def latex_visit_lean_code_goodies(self, node):
    pass

def latex_depart_lean_code_goodies(self, node):
    pass

# Extract code snippets for testing.

class LeanTestBuilder(Builder):
    '''
    Extract ``..code-block:: lean`` directives for testing.
    '''
    name = 'leantest'

    def init(self):
        self.written_files = set()

    def write_doc(self, docname, doctree):
        i = 0
        for node in doctree.traverse(lean_code_goodies):
            i += 1
            fn = os.path.join(self.outdir, '{0}_{1}.lean'.format(docname, i))
            self.written_files.add(fn)
            out = codecs.open(fn, 'w', encoding='utf-8')
            out.write(node['full_code'])

    def finish(self):
        for root, _, filenames in os.walk(self.outdir):
            for fn in fnmatch.filter(filenames, '*.lean'):
                fn = os.path.join(root, fn)
                if fn not in self.written_files:
                    os.remove(fn)

        proc = subprocess.Popen(['lean', '--make', self.outdir], stdout=subprocess.PIPE)
        stdout, stderr = proc.communicate()
        errors = '\n'.join(l for l in stdout.decode('utf-8').split('\n') if ': error:' in l)
        if errors != '': raise SphinxError('\nlean exited with errors:\n{0}\n'.format(errors))
        retcode = proc.wait()
        if retcode: raise SphinxError('lean exited with error code {0}'.format(retcode))

    def prepare_writing(self, docnames): pass

    def get_target_uri(self, docname, typ=None):
        return ''

    def get_outdated_docs(self):
        return self.env.found_docs

def setup(app):
    app.add_node(lean_code_goodies,
        html=(html_visit_lean_code_goodies, html_depart_lean_code_goodies),
        latex=(latex_visit_lean_code_goodies, latex_depart_lean_code_goodies))
    app.connect('doctree-resolved', process_lean_nodes)

    app.add_builder(LeanTestBuilder)

    return {'version': '0.1'}
