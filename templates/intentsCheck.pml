// This need to be automatically populated according to user's intents
never {
	do
	:: d[1].replicas < d[1].hpaSpec.minReplicas -> break
	:: else
	od;
}