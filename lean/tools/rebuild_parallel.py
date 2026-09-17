"""Build an extracted publication from source in a new, isolated output tree.

Only pinned third-party artifacts are reused. Every selected local source is
compiled exactly once. Failed dependencies block their consumers. No resume.
"""
from pathlib import Path
import argparse, concurrent.futures, hashlib, importlib.util, json, os, subprocess, time

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('release',type=Path)
    ap.add_argument('--jobs',type=int,default=2)
    ap.add_argument('--max-private-gib',type=float,default=24,
                    help='Per-compiler committed-memory ceiling on Windows')
    ap.add_argument('--build-name',default='.clean-build')
    args=ap.parse_args()
    assert args.jobs>=1 and args.max_private_gib>0
    root=args.release.resolve()
    spec=importlib.util.spec_from_file_location('release_rebuild',root/'tools/rebuild.py')
    rb=importlib.util.module_from_spec(spec);spec.loader.exec_module(rb)
    rb.BUILD=root/args.build_name;rb.LIB=rb.BUILD/'lib/lean';rb.LOGS=rb.BUILD/'logs';rb.SETUPS=rb.BUILD/'setup'
    assert rb.BUILD.parent==root and not rb.BUILD.exists()
    manifest=rb.load_manifest();modules,order,targets=rb.read_sources(manifest)
    info=rb.source_info(modules);rb.validate_graph(modules,order,info)
    rb.check_source_hashes(manifest,modules);rb.check_data_references(manifest)
    lean=rb.find_lean();prefix=rb.lean_prefix(lean)
    # Do not include the release's .lake/build or any project output directory.
    external=sorted(p/'.lake/build/lib/lean' for p in (root/'.lake/packages').iterdir() if p.is_dir())
    external=[p for p in external if p.is_dir()]+[prefix/'lib/lean']
    for path in external:
        assert not (path/'Borwein').exists(),path
    private_external={dep for i in info.values() for all_kw,dep in i['imports'] if all_kw and dep not in modules}
    external_arts=rb.artifact_inventory(external,private_external)
    assert not any(name in modules for name in external_arts)
    for p in (rb.LIB,rb.LOGS,rb.SETUPS):p.mkdir(parents=True,exist_ok=True)
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(str(p) for p in [rb.LIB,*external[:-1]])
    deps={n:{d for _,d in info[n]['imports'] if d in modules} for n in order}
    heavy={n for n in order if 'decide +kernel' in info[n]['text']}
    completed={};running={};pending=set(order);blocked=set();started=time.time()
    state={'status':'building','started_unix':started,'modules':[],'blocked':[],
           'initial_local_artifacts':0,'third_party_roots':[str(p) for p in external],
           'heavy_modules_run_exclusively':sorted(heavy),
           'jobs':args.jobs,'max_private_gib':args.max_private_gib,
           'lean_version':subprocess.check_output([str(lean),'--version'],cwd=root,text=True).strip()}
    def save():rb.write_json(rb.BUILD/'state.json',state)
    def run_compiler(cmd,log):
        peak=0;limited=False;started=time.perf_counter()
        with log.open('wb') as stream:
            flags={'creationflags':subprocess.CREATE_NO_WINDOW} if os.name=='nt' else {}
            proc=subprocess.Popen(cmd,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT,**flags)
            if os.name=='nt':
                import ctypes
                from ctypes import wintypes
                class Counters(ctypes.Structure):
                    _fields_=[('cb',wintypes.DWORD),('faults',wintypes.DWORD)]+[(n,ctypes.c_size_t) for n in
                        ['peak_working','working','peak_paged','paged','peak_nonpaged','nonpaged','pagefile','peak_pagefile','private']]
                getmem=ctypes.WinDLL('psapi').GetProcessMemoryInfo
                getmem.argtypes=[wintypes.HANDLE,ctypes.POINTER(Counters),wintypes.DWORD]
            while proc.poll() is None:
                if os.name=='nt':
                    counters=Counters();counters.cb=ctypes.sizeof(counters)
                    if getmem(int(proc._handle),ctypes.byref(counters),counters.cb):
                        peak=max(peak,counters.private)
                        if counters.private>args.max_private_gib*2**30:
                            limited=True;proc.terminate();break
                time.sleep(0.5)
            code=proc.wait()
            if limited:stream.write(b'\nBUILD RESOURCE LIMIT: compiler private memory exceeded the configured ceiling.\n')
        return code,time.perf_counter()-started,peak,limited
    def compile_one(name,arts):
        obj=rb.LIB/Path(*name.split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        log=rb.LOGS/(name.replace('.','_')+'.log');cmd=[str(lean)]
        if info[name]['mode']=='module':
            setup=rb.SETUPS/(name.replace('.','_')+'.json')
            rb.write_json(setup,{'name':name,'isModule':True,'imports':None,'importArts':arts,'dynlibs':[],'plugins':[],'options':{}})
            cmd.append('--setup='+str(setup))
        source=info[name]['path'];before=rb.digest(source)
        cmd+=['-o',str(obj),str(source)]
        code,seconds,peak,limited=run_compiler(cmd,log)
        assert rb.digest(source)==before,'Source changed during build: '+name
        row={'module':name,'source_sha256':before,'exit_code':code,'seconds':round(seconds,3),'log':log.relative_to(root).as_posix(),
             'peak_private_bytes':peak,'resource_limit_exceeded':limited}
        if code==0:
            assert obj.exists()
            row['output_sha256']=rb.digest(obj)
        return row
    save()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            failed={n for n,r in completed.items() if r['exit_code']!=0}|blocked
            changed=True
            while changed:
                bad={n for n in pending if deps[n]&failed};changed=bool(bad)
                blocked|=bad;pending-=bad;failed|=bad
            state['blocked']=sorted(blocked)
            ready=[n for n in order if n in pending and deps[n]<=completed.keys()]
            # Kernel reductions can retain large normal forms. Run one such
            # module alone, without changing any proof or evaluator settings.
            if any(n in heavy for n in running.values()):selected=[]
            elif ready and ready[0] in heavy:selected=ready[:1] if not running else []
            else:
                selected=[]
                for n in ready:
                    if n in heavy or len(selected)>=args.jobs-len(running):break
                    selected.append(n)
            for name in selected:
                arts={}
                if info[name]['mode']=='module':
                    private={d for a,d in info[name]['imports'] if a and d in modules}
                    arts=dict(external_arts)
                    # Read only completed outputs; never inspect a concurrent writer.
                    for n,row in completed.items():
                        if row['exit_code']!=0:continue
                        obj=rb.LIB/Path(*n.split('.')).with_suffix('.olean')
                        files=[str(obj)]
                        if obj.with_suffix('.ir').exists():
                            files.append(str(obj.with_suffix('.ir')))
                            if Path(str(obj)+'.server').exists():files.append(str(obj)+'.server')
                        if n in private:
                            assert len(files)==3 and Path(str(obj)+'.private').exists()
                            files.append(str(obj)+'.private')
                        arts[n]=files
                print('building '+name,flush=True)
                running[pool.submit(compile_one,name,arts)]=name;pending.remove(name)
            if not running:
                assert not pending,('No runnable modules',pending)
                break
            done,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
            for f in done:
                name=running.pop(f);row=f.result();completed[name]=row;state['modules'].append(row)
                print(('PASS ' if row['exit_code']==0 else 'FAIL ')+name,flush=True)
            save()
    if blocked or any(r['exit_code'] for r in completed.values()):
        state.update(status='failed',elapsed_seconds=round(time.time()-started,3));save();return 1
    # All sources must still have exactly the bytes actually compiled.
    rb.check_source_hashes(manifest,modules)
    audit=rb.BUILD/'audit.lean'
    assert not all(info[n]['mode']=='module' for n in order),'All-module audit needs explicit setup'
    audit.write_text(''.join('import '+n+'\n' for n in manifest['targets'])+'\n'+''.join('#print axioms '+t+'\n' for t in targets),encoding='utf-8')
    code,seconds=rb.run_logged([str(lean),str(audit)],rb.LOGS/'axioms.log',env)
    import re
    records=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",(rb.LOGS/'axioms.log').read_text(encoding='utf-8',errors='replace'))
    assert code==0 and [n for n,_ in records]==targets,'Final axiom audit failed'
    assert all({a.strip() for a in raw.split(',') if a.strip()}<=rb.ALLOWED_AXIOMS for _,raw in records)
    state.update(status='passed',audited_targets=targets,audit_seconds=seconds,elapsed_seconds=round(time.time()-started,3));save()
    print('PASS: '+str(len(completed))+' modules, '+str(len(targets))+' theorems',flush=True)
    return 0

if __name__=='__main__':raise SystemExit(main())
