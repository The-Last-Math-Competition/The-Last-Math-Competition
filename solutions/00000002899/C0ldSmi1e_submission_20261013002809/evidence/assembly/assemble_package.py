#!/usr/bin/env python3
"""Copy reviewed artifacts and create verified evidence archives; no Git/network/build."""
from pathlib import Path
import datetime
import gzip
import hashlib
import io
import json
import shutil
import tarfile

R = Path(__file__).resolve().parent
D = R.parent
TEX = '9385e6eaea23979033c1798b0ee0ea3c88d4b8ccc7e39a0582eb74b46a6cbab1'
PDF = 'af4e033139d5a3bc1aa45cb951bca89c291e76e573c58982e20027c87c145ba9'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def load(p):
    return json.loads(p.read_text())

def save(p, obj):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')

def main():
    assert __debug__, 'Assertions must be enabled'
    frozen = load(R/'frozen-review-manifest.json')
    assert load(R/'independent-review/engineering-verdict.json')['status'] == 'PASS'
    report = load(R/'independent-review/report-review.json')
    assert report['report']['tex_sha256'] == TEX and report['status'] == 'PASS'
    assert report['package_documentation']['readme_sha256'] == sha(R/'package-README.md')
    assert report['package_documentation']['verification_sha256'] == sha(R/'package-VERIFICATION.md')
    visual = load(R/'report/visual-review.json')
    assert visual['status'].startswith('PASS') and visual['tex_sha256'] == TEX and visual['pdf_sha256'] == PDF
    assert sha(R/'report/report.tex') == TEX and sha(R/'report/report.pdf') == PDF
    assert load(R/'root-final-public-guard-review.json')['status'].startswith('PASS')
    now = datetime.datetime.now(datetime.timezone.utc)
    package = R/'package'/('C0ldSmi1e_submission_'+now.strftime('%Y%m%d%H%M%S'))
    package.mkdir(parents=True, exist_ok=False)
    rows = []

    def copy(source, target):
        assert source.is_file() and not source.is_symlink()
        dest = package/target
        assert not dest.exists()
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, dest)
        assert sha(source) == sha(dest)
        rows.append({'source':str(source), 'path':target, 'sha256':sha(dest), 'size':dest.stat().st_size})

    for name, digest in frozen['files'].items():
        assert sha(R/'review-source/lean'/name) == digest
        copy(R/'review-source/lean'/name, 'lean/'+name)
    (package/'lean/.gitignore').write_text('.lake/\n')
    copy(R/'clean-author-input/00000002899.md', 'conjecture.md')
    for name in ['report.tex', 'report.pdf']:
        copy(R/'report'/name, name)
    for name in ['README', 'VERIFICATION']:
        copy(R/('package-'+name+'.md'), name+'.md')
    for name in ['frozen-review-manifest.json', 'verification-readiness.json',
                 'independent-stock-preparation.json', 'root-phase1-semantic-review.json',
                 'root-final-semantic-review.json', 'root-engineering-review.json']:
        copy(R/name, 'evidence/'+name)
    for name in ['lean-toolchain','lake-manifest.json']:
        copy(R/'expected-pins'/name, 'evidence/expected-pins/'+name)
    for source in sorted((R/'clean-author-input').iterdir()):
        copy(source, 'evidence/clean-author-input/'+source.name)
    for name in ['root-eligibility-review.json','root-metadata-match-classification.json','root-final-public-guard-review.json']:
        copy(R/name,'evidence/eligibility/'+name)
    for source in sorted((R/'independent-review').iterdir()):
        if source.is_file():
            assert source.suffix in {'.json','.txt','.py'}
            copy(source,'evidence/reviews/'+source.name)
    for name in ['build-receipt.json','build-stdout.txt','build-stderr.txt','report.log',
                 'extracted-text.txt','render-inventory.json','visual-review.json']:
        copy(R/'report'/name,'evidence/report/'+name)
    for page,digest in visual['pages'].items():
        name='inspected-'+page+'.png'
        assert sha(R/'report'/name)==digest
        copy(R/'report'/name,'evidence/report/'+name)
    ready=load(R/'verification-readiness.json')
    for name,digest in ready['verified_tool_hashes'].items():
        assert sha(D/'verification-tools-v2'/name)==digest
        copy(D/'verification-tools-v2'/name,'verification-tools-v2/'+name)
    copy(D/'verification-tools-v2/PROVENANCE.json','verification-tools-v2/PROVENANCE.json')
    copy(Path(__file__),'evidence/assembly/assemble_package.py')
    archives=[]

    def archive(stem, base, relative_files, label):
        sources=sorted(relative_files)
        members=[]
        dest=package/'evidence'/(stem+'.tar.gz')
        with dest.open('wb') as raw, gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=9) as zipped:
            with tarfile.open(fileobj=zipped,mode='w',format=tarfile.USTAR_FORMAT) as tar:
                for rel in sources:
                    source=base/rel
                    assert source.is_file() and not source.is_symlink()
                    assert source.suffix not in {'.olean','.ilean','.o','.a','.so','.dylib'}
                    assert not Path(rel).is_absolute() and '..' not in Path(rel).parts
                    data=source.read_bytes(); name=label+'/'+rel
                    info=tarfile.TarInfo(name);info.size=len(data);info.mtime=0
                    info.uid=info.gid=0;info.uname=info.gname='';info.mode=0o644
                    tar.addfile(info,io.BytesIO(data))
                    members.append({'path':name,'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
        manifest={'format':'gzip USTAR; sorted ordinary files; normalized metadata; gzip mtime0',
                  'source_directory':str(base),'files':members,'member_count':len(members)}
        save(package/'evidence'/(stem+'-manifest.json'),manifest)
        with tarfile.open(dest,'r:gz') as tar:
            actual=tar.getmembers();assert [m.name for m in actual]==[m['path'] for m in members]
            for m,row in zip(actual,members):
                assert m.isfile();b=tar.extractfile(m).read()
                assert len(b)==row['size'] and hashlib.sha256(b).hexdigest()==row['sha256']
        archives.append({'path':str(dest.relative_to(package)),'sha256':sha(dest),'members':len(members)})

    E=R/'independent-review/engineering'
    assert len(list((E/'receipts').glob('*.json')))==63
    assert len(list((E/'receipts').glob('*.stdout')))==len(list((E/'receipts').glob('*.stderr')))==63
    rawfiles=[p.relative_to(E).as_posix() for p in E.rglob('*') if p.is_file() and 'project' not in p.relative_to(E).parts]
    archive('engineering-records',E,rawfiles,'engineering')
    A=R/'author';author=load(A/'AUTHOR_ARTIFACT_SHA256.json')
    for name,digest in author.items():assert sha(A/name)==digest
    archive('author-records',A,[*author,'AUTHOR_ARTIFACT_SHA256.json'],'author')
    F=R/'final-public-guard'
    guardfiles=[p.relative_to(F).as_posix() for p in F.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
    archive('public-guard-records',F,guardfiles,'public-guard')
    assert sha(package/'conjecture.md')=='b35b46729894daad1186d415c977749787f14fb3cf84082532f4ab01a3947e28'
    for name,digest in frozen['files'].items():assert sha(package/'lean'/name)==digest
    inventory=[]
    for p in sorted(package.rglob('*')):
        if p.is_file():
            assert not p.is_symlink()
            inventory.append({'path':p.relative_to(package).as_posix(),'size':p.stat().st_size,'sha256':sha(p)})
    record={'status':'ASSEMBLED_PENDING_FINAL_PACKAGE_REVIEW','candidate':'00000002899',
            'assembled_at':now.isoformat(),'package':str(package),'assembly_script_sha256':sha(Path(__file__)),
            'frozen_manifest_sha256':sha(R/'frozen-review-manifest.json'),'tex_sha256':TEX,'pdf_sha256':PDF,
            'copied_inputs':rows,'archives':archives,'content_inventory':inventory,
            'inventory_excludes':['package-preparation.json','SHA256SUMS'],
            'scope':'Only personal submission artifacts; no source/config edits, build, Git or network operation by assembler.',
            'pending':['Independent assembled-package review','Publication after exact Git scope and remote-state checks']}
    save(package/'package-preparation.json',record)
    files=[p for p in sorted(package.rglob('*')) if p.is_file()]
    (package/'SHA256SUMS').write_text(''.join(sha(p)+'  '+p.relative_to(package).as_posix()+'\n' for p in files))
    print(json.dumps({'status':record['status'],'package':str(package),'file_count':len(files)+1,'archives':archives},indent=2))

if __name__=='__main__':
    main()
