# Frozen layer-21 probe selection

This configuration was fixed after the original contrast-v1 set was demoted
from test data to development data.  A post-hoc sweep on contrast v1 selected:

- layer: 21
- pooling: mean over prompt tokens
- ridge: 0.1
- contrast-v1 accuracy: 70/100
- paraphrase validation accuracy: 48/80

That 70/100 result is not promotable because its labels selected the
configuration.  The purpose of this sealed probe is a single evaluation on a
newly authored contrast-v2 set whose prompts did not exist when the probe was
sealed.

Selection evidence:

- `runs/iter037-frozen-method-probe-iter014/report.json`
- report SHA-256: `df0f37b8cde4c537bd647af77712ff3b0b48bbe4b4e9c2f6ea1efbac0a860ba7`
- probe SHA-256: `760b0f62d541fda7511926fccaee6ec4576760e50e1d58191fb73e9f3eb8a8aa`
- selection-seal SHA-256: `e5c8f2715e875ae99ff1d53b053120824b611233701eba180e7f18d3790162c3`

No contrast-v2 model evaluation may be used to alter this configuration.
