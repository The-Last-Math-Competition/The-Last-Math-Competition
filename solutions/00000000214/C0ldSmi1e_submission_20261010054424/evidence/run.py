import os,sys,pathlib,subprocess,json,hashlib,datetime
root=pathlib.Path('/private/tmp/tlmc214-author')
stock=pathlib.Path('/private/tmp/tlmc-standard-library-419/mathlib')
paths=[root,stock/'.lake/build/lib/lean']+list((stock/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,paths))
src=pathlib.Path(sys.argv[1]); count=len(list((root/'logs').glob('run-*')))+1
out=root/'logs'/f'run-{count:04d}';out.mkdir()
(out/src.name).write_bytes(src.read_bytes())
cmd=['/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin/lean']+sys.argv[1:]
p=subprocess.run(cmd,env=env,cwd=root,text=True,capture_output=True)
(out/'stdout.txt').write_text(p.stdout);(out/'stderr.txt').write_text(p.stderr)
(out/'receipt.json').write_text(json.dumps({'command':cmd,'exit':p.returncode,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'LEAN_PATH':env['LEAN_PATH']},indent=2))
print(f'run-{count:04d} exit={p.returncode}\n'+p.stdout+p.stderr)
sys.exit(p.returncode)
