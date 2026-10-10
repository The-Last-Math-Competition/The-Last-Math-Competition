import os,sys,pathlib,subprocess,json,hashlib,datetime,shutil
root=pathlib.Path('/private/tmp/tlmc214-proof')
evid=root/'evidence';count=1
while True:
 out=evid/f'check-{count:04d}'
 try:
  out.mkdir();break
 except FileExistsError:
  count+=1
for f in list((root/'TLMC214').glob('*.lean'))+[root/'TLMC214.lean',root/'lakefile.lean',root/'CheckAxioms.lean']:
 d=out/'sources'/f.relative_to(root);d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,d)
env=os.environ.copy();env['PATH']='/private/tmp/tlmc310-runtime/lean-4.19.0-darwin_aarch64/bin:'+env['PATH']
cmd=sys.argv[1:];p=subprocess.run(cmd,cwd=root,env=env,text=True,capture_output=True)
(out/'stdout.txt').write_text(p.stdout);(out/'stderr.txt').write_text(p.stderr)
(out/'receipt.json').write_text(json.dumps({'command':cmd,'exit':p.returncode,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'cwd':str(root)},indent=2)+'\n')
print(str(out)+' exit='+str(p.returncode)+'\n'+p.stdout+p.stderr);sys.exit(p.returncode)
